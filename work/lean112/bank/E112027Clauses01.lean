import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 3 = true ∨ valuation q 8 = true := by
  rw [value3, value6, value8, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(2 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (19 : Vertex) [(2 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 124 = true ∨ valuation q 3 = true ∨ valuation q 7 = true := by
  rw [value3, value6, value7, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(2 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(2 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 5 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ∈ [(17 : Vertex), (18 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (19 : Vertex) [(17 : Vertex), (18 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 6 = true := by
  rw [value6, value7, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 5 = true := by
  rw [value5, value7, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(17 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (18 : Vertex) [(17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 8 = true := by
  rw [value8, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (22 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 4 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ∈ [(6 : Vertex), (18 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (22 : Vertex) [(6 : Vertex), (18 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 6 = true := by
  rw [value6, value8, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 4 = true := by
  rw [value4, value8, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 35 = false ∨ valuation q 64 = false := by
  rw [value2, value9, value35, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (193 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 35 = true ∨ valuation q 64 = true := by
  rw [value9, value35, value64, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(193 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (1 : Vertex) [(193 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 2 = true ∨ valuation q 64 = true := by
  rw [value2, value9, value64, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(1 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (193 : Vertex) [(1 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 128 = true ∨ valuation q 11 = true := by
  rw [value10, value11, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (2 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 37 = false := by
  rw [value4, value11, value14, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (78 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 66 = false := by
  rw [value4, value11, value14, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (78 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 4 = false ∨ valuation q 37 = false ∨ valuation q 66 = false := by
  rw [value4, value11, value37, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (198 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 14 = false ∨ valuation q 37 = false := by
  rw [value10, value11, value14, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (66 : Vertex) (78 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 14 = false ∨ valuation q 66 = false := by
  rw [value10, value11, value14, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (66 : Vertex) (78 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 37 = false ∨ valuation q 66 = false := by
  rw [value10, value11, value37, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (66 : Vertex) (198 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 37 = false ∨ valuation q 66 = false := by
  rw [value11, value14, value37, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (78 : Vertex) (198 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 39 = false ∨ valuation q 68 = false := by
  rw [value12, value13, value39, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (76 : Vertex) (200 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 39 = true ∨ valuation q 68 = true := by
  rw [value12, value39, value68, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(200 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (76 : Vertex) [(200 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 39 = true := by
  rw [value12, value13, value39, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(76 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (328 : Vertex) [(76 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 13 = true := by
  rw [value13, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (76 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = true ∨ valuation q 14 = true := by
  rw [value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (78 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (76 : Vertex) [(72 : Vertex), (78 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 14 = true := by
  rw [value13, value14, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(78 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (72 : Vertex) [(78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 12 = true := by
  rw [value12, value13, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(72 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (78 : Vertex) [(72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 132 = true ∨ valuation q 11 = true := by
  rw [value11, value14, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (76 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value1, value15, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 21 = false := by
  rw [value1, value15, value16, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 26 = false := by
  rw [value1, value15, value16, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 26 = false ∨ valuation q 34 = false := by
  rw [value1, value15, value26, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (144 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E027.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112027
