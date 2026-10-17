import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 125 = true ∨ valuation q 18 = true ∨ valuation q 20 = true := by
  rw [value18, value19, value20, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(64 : Vertex), (69 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (73 : Vertex) [(64 : Vertex), (69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 126 = true ∨ valuation q 21 = true := by
  rw [value20, value21, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(71 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (65 : Vertex) [(71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 126 = true ∨ valuation q 19 = true := by
  rw [value19, value20, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(65 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (71 : Vertex) [(65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 127 = true ∨ valuation q 25 = true := by
  rw [value21, value25, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (69 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 4 = false ∨ valuation q 18 = false ∨ valuation q 52 = false := by
  rw [value4, value18, value22, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (8 : Vertex) (64 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 4 = false ∨ valuation q 23 = false ∨ valuation q 52 = false := by
  rw [value4, value22, value23, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (8 : Vertex) (73 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 23 = false ∨ valuation q 52 = false := by
  rw [value18, value22, value23, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (73 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 128 = true ∨ valuation q 4 = true ∨ valuation q 18 = true ∨ valuation q 23 = true := by
  rw [value4, value18, value22, value23, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(8 : Vertex), (64 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (200 : Vertex) [(8 : Vertex), (64 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 5 = true ∨ valuation q 19 = true ∨ valuation q 22 = true := by
  rw [value5, value19, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ∈ [(9 : Vertex), (65 : Vertex), (72 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (73 : Vertex) [(9 : Vertex), (65 : Vertex), (72 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 129 = true ∨ valuation q 19 = true ∨ valuation q 22 = true := by
  rw [value19, value22, value23, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(65 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (9 : Vertex) [(65 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 129 = true ∨ valuation q 5 = true ∨ valuation q 22 = true := by
  rw [value5, value22, value23, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(9 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (65 : Vertex) [(9 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 129 = true ∨ valuation q 5 = true ∨ valuation q 19 = true := by
  rw [value5, value19, value23, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(9 : Vertex), (65 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (72 : Vertex) [(9 : Vertex), (65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 8 = false ∨ valuation q 25 = false ∨ valuation q 32 = false := by
  rw [value8, value24, value25, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (79 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value18, value26, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (64 : Vertex) (82 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 132 = true ∨ valuation q 18 = true ∨ valuation q 29 = true := by
  rw [value18, value26, value29, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(64 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (82 : Vertex) [(64 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 132 = true ∨ valuation q 18 = true ∨ valuation q 27 = true := by
  rw [value18, value26, value27, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(64 : Vertex), (82 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (84 : Vertex) [(64 : Vertex), (82 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 27 = true := by
  rw [value27, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (82 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 133 = true ∨ valuation q 28 = true := by
  rw [value27, value28, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(83 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (80 : Vertex) [(83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 133 = true ∨ valuation q 26 = true := by
  rw [value26, value27, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(80 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (83 : Vertex) [(80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 9 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value9, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (82 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 134 = true ∨ valuation q 9 = true ∨ valuation q 30 = true := by
  rw [value9, value28, value30, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(19 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (82 : Vertex) [(19 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 29 = true := by
  rw [value29, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (84 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 135 = true ∨ valuation q 31 = true := by
  rw [value29, value31, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 135 = true ∨ valuation q 26 = true := by
  rw [value26, value29, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(80 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (92 : Vertex) [(80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 30 = true := by
  rw [value30, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (91 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 56 = false := by
  rw [value28, value30, value33, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (83 : Vertex) (95 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 137 = true ∨ valuation q 32 = true := by
  rw [value31, value32, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(94 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (84 : Vertex) [(94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 137 = true ∨ valuation q 29 = true := by
  rw [value29, value31, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (92 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (92 : Vertex) (94 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 138 = true ∨ valuation q 31 = true ∨ valuation q 33 = true := by
  rw [value31, value32, value33, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(92 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (78 : Vertex) [(92 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 138 = true ∨ valuation q 24 = true ∨ valuation q 33 = true := by
  rw [value24, value32, value33, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(78 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (92 : Vertex) [(78 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 138 = true ∨ valuation q 24 = true ∨ valuation q 31 = true := by
  rw [value24, value31, value32, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(78 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (95 : Vertex) [(78 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 139 = true ∨ valuation q 25 = true ∨ valuation q 30 = true := by
  rw [value25, value30, value33, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(79 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (94 : Vertex) [(79 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E091.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112091
