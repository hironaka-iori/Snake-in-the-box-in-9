import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value12, value13, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 81 = false := by
  rw [value12, value13, value14, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 22 = false := by
  rw [value12, value13, value18, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 81 = false := by
  rw [value12, value13, value18, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 81 = false := by
  rw [value12, value13, value22, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 22 = false := by
  rw [value12, value14, value18, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 81 = false := by
  rw [value12, value14, value18, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 81 = false := by
  rw [value12, value14, value22, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 81 = false := by
  rw [value12, value18, value22, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 18 = false ∨ valuation q 22 = false := by
  rw [value18, value22, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 133 = true ∨ valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 22 = true ∨ valuation q 81 = true := by
  rw [value12, value14, value18, value22, value81, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(162 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(162 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 133 = true ∨ valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 81 = true := by
  rw [value12, value13, value14, value18, value81, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(161 : Vertex), (162 : Vertex), (168 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (176 : Vertex) [(161 : Vertex), (162 : Vertex), (168 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 16 = false := by
  rw [value12, value13, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 23 = false := by
  rw [value12, value13, value16, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 23 = false ∨ valuation q 82 = false := by
  rw [value12, value13, value23, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (177 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 23 = false := by
  rw [value13, value15, value16, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (163 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 23 = false ∨ valuation q 82 = false := by
  rw [value13, value16, value23, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (165 : Vertex) (177 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 134 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 23 = true ∨ valuation q 82 = true := by
  rw [value13, value15, value16, value23, value82, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(163 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 134 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 23 = true ∨ valuation q 82 = true := by
  rw [value12, value13, value16, value23, value82, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(160 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (163 : Vertex) [(160 : Vertex), (165 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 134 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 23 = true ∨ valuation q 82 = true := by
  rw [value12, value13, value15, value23, value82, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (165 : Vertex) [(160 : Vertex), (163 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 134 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 82 = true := by
  rw [value12, value13, value15, value16, value82, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (177 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 134 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 23 = true := by
  rw [value12, value13, value15, value16, value23, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (417 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value12, value14, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 17 = false ∨ valuation q 32 = false := by
  rw [value12, value14, value17, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (166 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value12, value14, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 12 = false ∨ valuation q 24 = false ∨ valuation q 83 = false := by
  rw [value12, value14, value24, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 24 = false := by
  rw [value14, value15, value17, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (163 : Vertex) (166 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 24 = true ∨ valuation q 32 = true ∨ valuation q 83 = true := by
  rw [value12, value14, value15, value24, value32, value83, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (178 : Vertex), (226 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (166 : Vertex) [(160 : Vertex), (163 : Vertex), (178 : Vertex), (226 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 24 = true ∨ valuation q 83 = true := by
  rw [value12, value14, value15, value17, value24, value83, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (226 : Vertex) [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 24 = true ∨ valuation q 32 = true := by
  rw [value12, value14, value15, value17, value24, value32, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (418 : Vertex) [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value1, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (162 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 13 = false ∨ valuation q 19 = false := by
  rw [value1, value13, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (35 : Vertex) (161 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E024.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112024
