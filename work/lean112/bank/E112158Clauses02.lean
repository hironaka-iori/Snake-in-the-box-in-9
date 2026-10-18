import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 133 = true ∨ valuation q 19 = true ∨ valuation q 24 = true ∨ valuation q 54 = true := by
  rw [value15, value19, value24, value54, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(79 : Vertex), (87 : Vertex), (199 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (67 : Vertex) [(79 : Vertex), (87 : Vertex), (199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 133 = true ∨ valuation q 13 = true ∨ valuation q 24 = true ∨ valuation q 54 = true := by
  rw [value13, value15, value24, value54, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(67 : Vertex), (87 : Vertex), (199 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (79 : Vertex) [(67 : Vertex), (87 : Vertex), (199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 55 = false := by
  rw [value16, value17, value25, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (73 : Vertex) (88 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 17 = false ∨ valuation q 25 = false := by
  rw [value17, value25, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (72 : Vertex) (73 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 134 = true ∨ valuation q 25 = true ∨ valuation q 55 = true := by
  rw [value16, value25, value55, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(88 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (73 : Vertex) [(88 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 134 = true ∨ valuation q 17 = true ∨ valuation q 55 = true := by
  rw [value16, value17, value55, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(73 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (88 : Vertex) [(73 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 134 = true ∨ valuation q 17 = true ∨ valuation q 25 = true := by
  rw [value16, value17, value25, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(73 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (200 : Vertex) [(73 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 26 = false := by
  rw [value12, value16, value17, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (72 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 16 = true ∨ valuation q 26 = true := by
  rw [value16, value17, value26, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(72 : Vertex), (89 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (65 : Vertex) [(72 : Vertex), (89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 26 = true := by
  rw [value12, value17, value26, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(65 : Vertex), (89 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (72 : Vertex) [(65 : Vertex), (89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 16 = true := by
  rw [value12, value16, value17, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(65 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (89 : Vertex) [(65 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 18 = true := by
  rw [value18, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (78 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = true ∨ valuation q 59 = true := by
  rw [value18, value19, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ∈ [(79 : Vertex), (206 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (78 : Vertex) [(79 : Vertex), (206 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 19 = false ∨ valuation q 59 = false := by
  rw [value19, value59, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (78 : Vertex) (79 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 136 = true ∨ valuation q 59 = true := by
  rw [value18, value59, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (79 : Vertex) [(206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 136 = true ∨ valuation q 19 = true := by
  rw [value18, value19, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (206 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 60 = false := by
  rw [value15, value18, value19, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (78 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 4 = true ∨ valuation q 18 = true ∨ valuation q 60 = true := by
  rw [value4, value18, value19, value60, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(15 : Vertex), (78 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (71 : Vertex) [(15 : Vertex), (78 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 4 = true ∨ valuation q 15 = true ∨ valuation q 60 = true := by
  rw [value4, value15, value19, value60, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(15 : Vertex), (71 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (78 : Vertex) [(15 : Vertex), (71 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 4 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value4, value15, value18, value19, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(15 : Vertex), (71 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (207 : Vertex) [(15 : Vertex), (71 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 27 = true := by
  rw [value20, value27, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (86 : Vertex) → w ∈ [(90 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (86 : Vertex) [(90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 23 = true := by
  rw [value20, value23, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(86 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (90 : Vertex) [(86 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 14 = false ∨ valuation q 23 = false ∨ valuation q 64 = false := by
  rw [value14, value21, value23, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (86 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 64 = false := by
  rw [value21, value22, value23, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (85 : Vertex) (86 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 64 = true := by
  rw [value21, value22, value23, value64, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(85 : Vertex), (86 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(85 : Vertex), (86 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 64 = true := by
  rw [value14, value21, value22, value64, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (86 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (86 : Vertex) [(68 : Vertex), (85 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value14, value21, value22, value23, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex), (86 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (212 : Vertex) [(68 : Vertex), (85 : Vertex), (86 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value7, value21, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (21 : Vertex) (84 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value7, value21, value22, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (21 : Vertex) (84 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 65 = false := by
  rw [value7, value21, value22, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (21 : Vertex) (84 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 24 = false ∨ valuation q 28 = false := by
  rw [value7, value22, value24, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (21 : Vertex) (87 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 24 = false ∨ valuation q 65 = false := by
  rw [value7, value22, value24, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (21 : Vertex) (87 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E158.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112158
