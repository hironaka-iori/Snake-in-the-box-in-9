import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 130 = true ∨ valuation q 8 = true ∨ valuation q 10 = true := by
  rw [value8, value9, value10, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(68 : Vertex), (71 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (77 : Vertex) [(68 : Vertex), (71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 14 = false := by
  rw [value7, value9, value10, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (69 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 43 = false := by
  rw [value7, value9, value10, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (69 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 43 = false := by
  rw [value7, value10, value14, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (79 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 43 = false := by
  rw [value9, value10, value14, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (69 : Vertex) (79 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 131 = true ∨ valuation q 7 = true ∨ valuation q 14 = true ∨ valuation q 43 = true := by
  rw [value7, value10, value14, value43, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(67 : Vertex), (79 : Vertex), (199 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (69 : Vertex) [(67 : Vertex), (79 : Vertex), (199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 131 = true ∨ valuation q 7 = true ∨ valuation q 9 = true ∨ valuation q 14 = true := by
  rw [value7, value9, value10, value14, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (71 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(67 : Vertex), (69 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (71 : Vertex) (199 : Vertex) [(67 : Vertex), (69 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 12 = true := by
  rw [value3, value6, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ∈ [(10 : Vertex), (66 : Vertex), (75 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (74 : Vertex) [(10 : Vertex), (66 : Vertex), (75 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 132 = true ∨ valuation q 6 = true ∨ valuation q 12 = true := by
  rw [value6, value11, value12, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(66 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (10 : Vertex) [(66 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 132 = true ∨ valuation q 3 = true ∨ valuation q 12 = true := by
  rw [value3, value11, value12, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(10 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (66 : Vertex) [(10 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 132 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value11, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(10 : Vertex), (66 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (75 : Vertex) [(10 : Vertex), (66 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 14 = false := by
  rw [value7, value11, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (74 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 46 = false := by
  rw [value7, value11, value12, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (74 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 67 = false := by
  rw [value7, value11, value12, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (74 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 46 = false := by
  rw [value7, value12, value14, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (79 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 67 = false := by
  rw [value7, value12, value14, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (79 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 7 = false ∨ valuation q 46 = false ∨ valuation q 67 = false := by
  rw [value7, value12, value46, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (67 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 46 = false := by
  rw [value11, value12, value14, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (74 : Vertex) (79 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 67 = false := by
  rw [value11, value12, value14, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (74 : Vertex) (79 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 46 = false ∨ valuation q 67 = false := by
  rw [value11, value12, value46, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (74 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 46 = false ∨ valuation q 67 = false := by
  rw [value12, value14, value46, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (75 : Vertex) (79 : Vertex) (203 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 133 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 46 = true ∨ valuation q 67 = true := by
  rw [value11, value12, value14, value46, value67, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(74 : Vertex), (79 : Vertex), (203 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (67 : Vertex) [(74 : Vertex), (79 : Vertex), (203 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 133 = true ∨ valuation q 7 = true ∨ valuation q 14 = true ∨ valuation q 46 = true ∨ valuation q 67 = true := by
  rw [value7, value12, value14, value46, value67, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(67 : Vertex), (79 : Vertex), (203 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (74 : Vertex) [(67 : Vertex), (79 : Vertex), (203 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 133 = true ∨ valuation q 7 = true ∨ valuation q 11 = true ∨ valuation q 46 = true ∨ valuation q 67 = true := by
  rw [value7, value11, value12, value46, value67, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(67 : Vertex), (74 : Vertex), (203 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (79 : Vertex) [(67 : Vertex), (74 : Vertex), (203 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 133 = true ∨ valuation q 7 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 67 = true := by
  rw [value7, value11, value12, value14, value67, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(67 : Vertex), (74 : Vertex), (79 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (203 : Vertex) [(67 : Vertex), (74 : Vertex), (79 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 133 = true ∨ valuation q 7 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 46 = true := by
  rw [value7, value11, value12, value14, value46, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(67 : Vertex), (74 : Vertex), (79 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (331 : Vertex) [(67 : Vertex), (74 : Vertex), (79 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 134 = true ∨ valuation q 14 = true := by
  rw [value13, value14, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (69 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 134 = true ∨ valuation q 9 = true := by
  rw [value9, value13, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(69 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (79 : Vertex) [(69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value10, value12, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (77 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 22 = false := by
  rw [value10, value12, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 22 = false := by
  rw [value10, value13, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (77 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 22 = false := by
  rw [value12, value13, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (75 : Vertex) (77 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E019.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112019
