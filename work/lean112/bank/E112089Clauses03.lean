import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 2 = false ∨ valuation q 24 = false ∨ valuation q 56 = false := by
  rw [value2, value19, value24, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (73 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 56 = false := by
  rw [value18, value19, value24, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (64 : Vertex) (73 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 2 = true ∨ valuation q 18 = true ∨ valuation q 56 = true := by
  rw [value2, value18, value19, value56, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(1 : Vertex), (64 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (73 : Vertex) [(1 : Vertex), (64 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 57 = false := by
  rw [value18, value20, value22, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (66 : Vertex) (64 : Vertex) (70 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 144 = true ∨ valuation q 18 = true ∨ valuation q 57 = true := by
  rw [value18, value20, value57, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(64 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (70 : Vertex) [(64 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 144 = true ∨ valuation q 18 = true ∨ valuation q 22 = true := by
  rw [value18, value20, value22, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(64 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (194 : Vertex) [(64 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value18, value21, value22, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (64 : Vertex) (70 : Vertex) (76 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 29 = false := by
  rw [value18, value21, value22, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (64 : Vertex) (70 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 18 = false ∨ valuation q 25 = false ∨ valuation q 29 = false := by
  rw [value18, value21, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (64 : Vertex) (76 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 29 = false := by
  rw [value21, value22, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (70 : Vertex) (76 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 29 = true := by
  rw [value21, value22, value25, value29, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (64 : Vertex) → w ∈ [(70 : Vertex), (76 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (64 : Vertex) [(70 : Vertex), (76 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 18 = true ∨ valuation q 25 = true ∨ valuation q 29 = true := by
  rw [value18, value21, value25, value29, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(64 : Vertex), (76 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (70 : Vertex) [(64 : Vertex), (76 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 18 = true ∨ valuation q 22 = true ∨ valuation q 25 = true := by
  rw [value18, value21, value22, value25, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(64 : Vertex), (70 : Vertex), (76 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(64 : Vertex), (70 : Vertex), (76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 22 = true := by
  rw [value22, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (70 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 26 = true ∨ valuation q 60 = true := by
  rw [value20, value21, value22, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ∈ [(66 : Vertex), (68 : Vertex), (78 : Vertex), (198 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (70 : Vertex) [(66 : Vertex), (68 : Vertex), (78 : Vertex), (198 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value20, value22, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (66 : Vertex) (78 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 60 = false := by
  rw [value21, value22, value26, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (68 : Vertex) (78 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 21 = true ∨ valuation q 26 = true ∨ valuation q 60 = true := by
  rw [value21, value22, value26, value60, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(68 : Vertex), (78 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (66 : Vertex) [(68 : Vertex), (78 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 26 = true ∨ valuation q 60 = true := by
  rw [value20, value22, value26, value60, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(66 : Vertex), (78 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (68 : Vertex) [(66 : Vertex), (78 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 60 = true := by
  rw [value20, value21, value22, value60, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(66 : Vertex), (68 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (78 : Vertex) [(66 : Vertex), (68 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 26 = true := by
  rw [value20, value21, value22, value26, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(66 : Vertex), (68 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (198 : Vertex) [(66 : Vertex), (68 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value18, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (73 : Vertex) (76 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value18, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (73 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 62 = false := by
  rw [value18, value23, value24, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (73 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 18 = false ∨ valuation q 25 = false ∨ valuation q 32 = false := by
  rw [value18, value23, value25, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (76 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 62 = false := by
  rw [value18, value23, value32, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (88 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 32 = false := by
  rw [value23, value24, value25, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (73 : Vertex) (76 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 62 = false := by
  rw [value23, value24, value25, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (73 : Vertex) (76 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 32 = false ∨ valuation q 62 = false := by
  rw [value23, value24, value32, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (73 : Vertex) (88 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 32 = false ∨ valuation q 62 = false := by
  rw [value23, value25, value32, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (76 : Vertex) (88 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 18 = true ∨ valuation q 25 = true ∨ valuation q 32 = true ∨ valuation q 62 = true := by
  rw [value18, value23, value25, value32, value62, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(64 : Vertex), (76 : Vertex), (88 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (73 : Vertex) [(64 : Vertex), (76 : Vertex), (88 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 18 = true ∨ valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 62 = true := by
  rw [value18, value23, value24, value25, value62, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(64 : Vertex), (73 : Vertex), (76 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (88 : Vertex) [(64 : Vertex), (73 : Vertex), (76 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E089.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112089
