import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 123 = true ∨ valuation q 16 = true ∨ valuation q 66 = true := by
  rw [value15, value16, value66, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(28 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (16 : Vertex) [(28 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 123 = true ∨ valuation q 10 = true ∨ valuation q 66 = true := by
  rw [value10, value15, value66, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(16 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (28 : Vertex) [(16 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 123 = true ∨ valuation q 10 = true ∨ valuation q 16 = true := by
  rw [value10, value15, value16, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(16 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (280 : Vertex) [(16 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value15, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (24 : Vertex) (29 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 124 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value16, value18, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(24 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(24 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 124 = true ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value15, value16, value17, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(24 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(24 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 125 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value17, value19, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(28 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (13 : Vertex) [(28 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 125 = true ∨ valuation q 8 = true ∨ valuation q 19 = true := by
  rw [value8, value17, value19, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(13 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (28 : Vertex) [(13 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 125 = true ∨ valuation q 8 = true ∨ valuation q 16 = true := by
  rw [value8, value16, value17, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(13 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (31 : Vertex) [(13 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value14, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (30 : Vertex) (22 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 126 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value18, value19, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(28 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (22 : Vertex) [(28 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 126 = true ∨ valuation q 14 = true ∨ valuation q 19 = true := by
  rw [value14, value18, value19, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(22 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (28 : Vertex) [(22 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 126 = true ∨ valuation q 14 = true ∨ valuation q 16 = true := by
  rw [value14, value16, value18, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(22 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (31 : Vertex) [(22 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value9, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 31 = false := by
  rw [value9, value17, value19, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 69 = false := by
  rw [value9, value17, value19, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (29 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 31 = false := by
  rw [value9, value18, value19, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (30 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 9 = false ∨ valuation q 18 = false ∨ valuation q 69 = false := by
  rw [value9, value18, value19, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (30 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 31 = false := by
  rw [value17, value18, value19, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (30 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 69 = false := by
  rw [value17, value18, value19, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (29 : Vertex) (30 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 128 = true ∨ valuation q 23 = true := by
  rw [value20, value23, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (2 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 128 = true ∨ valuation q 3 = true := by
  rw [value3, value20, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(2 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (70 : Vertex) [(2 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 5 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value5, value21, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value6, value20, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (66 : Vertex) (68 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 70 = false := by
  rw [value6, value21, value23, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (68 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 70 = false := by
  rw [value20, value21, value23, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (66 : Vertex) (68 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 7 = false ∨ valuation q 30 = false ∨ valuation q 72 = false := by
  rw [value7, value24, value30, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (11 : Vertex) (91 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 132 = true ∨ valuation q 30 = true ∨ valuation q 72 = true := by
  rw [value24, value30, value72, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(91 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (11 : Vertex) [(91 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 132 = true ∨ valuation q 7 = true ∨ valuation q 72 = true := by
  rw [value7, value24, value72, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(11 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (91 : Vertex) [(11 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 133 = true := by
  rw [value25, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 75 = false := by
  rw [value21, value26, value27, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (85 : Vertex) (340 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value22, value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (69 : Vertex) (84 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E185.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112185
