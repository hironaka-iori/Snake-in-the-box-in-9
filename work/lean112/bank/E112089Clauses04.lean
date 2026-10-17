import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 18 = true ∨ valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 32 = true := by
  rw [value18, value23, value24, value25, value32, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(64 : Vertex), (73 : Vertex), (76 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (200 : Vertex) [(64 : Vertex), (73 : Vertex), (76 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 23 = false := by
  rw [value6, value19, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (9 : Vertex) (65 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 63 = false := by
  rw [value6, value23, value24, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (9 : Vertex) (72 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 63 = false := by
  rw [value19, value23, value24, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (72 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 19 = true ∨ valuation q 23 = true ∨ valuation q 63 = true := by
  rw [value19, value23, value24, value63, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(65 : Vertex), (72 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (9 : Vertex) [(65 : Vertex), (72 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 6 = true ∨ valuation q 23 = true ∨ valuation q 63 = true := by
  rw [value6, value23, value24, value63, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(9 : Vertex), (72 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (65 : Vertex) [(9 : Vertex), (72 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 6 = true ∨ valuation q 19 = true ∨ valuation q 63 = true := by
  rw [value6, value19, value24, value63, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(9 : Vertex), (65 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (72 : Vertex) [(9 : Vertex), (65 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 6 = true ∨ valuation q 19 = true ∨ valuation q 23 = true := by
  rw [value6, value19, value23, value24, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(9 : Vertex), (65 : Vertex), (72 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (201 : Vertex) [(9 : Vertex), (65 : Vertex), (72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 25 = true := by
  rw [value25, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (76 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 88 = false := by
  rw [value21, value23, value25, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (68 : Vertex) (72 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 88 = false := by
  rw [value21, value25, value26, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (68 : Vertex) (78 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 65 = false ∨ valuation q 88 = false := by
  rw [value21, value25, value65, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (68 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 88 = false := by
  rw [value23, value25, value26, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (72 : Vertex) (78 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 65 = false ∨ valuation q 88 = false := by
  rw [value23, value25, value65, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (72 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 65 = false ∨ valuation q 88 = false := by
  rw [value25, value26, value65, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (78 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 26 = true ∨ valuation q 65 = true := by
  rw [value21, value23, value25, value26, value65, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(68 : Vertex), (72 : Vertex), (78 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (332 : Vertex) [(68 : Vertex), (72 : Vertex), (78 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value10, value22, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (70 : Vertex) (76 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value10, value22, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (70 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 67 = false := by
  rw [value10, value22, value26, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (70 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value10, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (76 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 67 = false := by
  rw [value10, value25, value26, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (76 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 10 = false ∨ valuation q 27 = false ∨ valuation q 67 = false := by
  rw [value10, value26, value27, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (79 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value22, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (76 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 67 = false := by
  rw [value22, value25, value26, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (76 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 27 = false ∨ valuation q 67 = false := by
  rw [value22, value26, value27, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (70 : Vertex) (79 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 67 = false := by
  rw [value25, value26, value27, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (76 : Vertex) (79 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 67 = true := by
  rw [value22, value25, value26, value27, value67, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(70 : Vertex), (76 : Vertex), (79 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (14 : Vertex) [(70 : Vertex), (76 : Vertex), (79 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 10 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 67 = true := by
  rw [value10, value25, value26, value27, value67, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(14 : Vertex), (76 : Vertex), (79 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [(14 : Vertex), (76 : Vertex), (79 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 10 = true ∨ valuation q 22 = true ∨ valuation q 27 = true ∨ valuation q 67 = true := by
  rw [value10, value22, value26, value27, value67, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(14 : Vertex), (70 : Vertex), (79 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (76 : Vertex) [(14 : Vertex), (70 : Vertex), (79 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 150 = true ∨ valuation q 10 = true ∨ valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 67 = true := by
  rw [value10, value22, value25, value26, value67, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(14 : Vertex), (70 : Vertex), (76 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (79 : Vertex) [(14 : Vertex), (70 : Vertex), (76 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = true ∨ valuation q 35 = true ∨ valuation q 68 = true := by
  rw [value26, value27, value35, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ∈ [(78 : Vertex), (95 : Vertex), (207 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (79 : Vertex) [(78 : Vertex), (95 : Vertex), (207 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 35 = false ∨ valuation q 68 = false := by
  rw [value26, value27, value35, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (78 : Vertex) (95 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E089.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112089
