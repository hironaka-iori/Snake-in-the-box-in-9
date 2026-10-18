import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 123 = true ∨ valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 73 = true := by
  rw [value3, value5, value7, value73, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(103 : Vertex), (107 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (109 : Vertex) [(103 : Vertex), (107 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 11 = true := by
  rw [value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ∈ [(126 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (118 : Vertex) [(126 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 8 = true := by
  rw [value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 125 = true ∨ valuation q 10 = true := by
  rw [value9, value10, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 6 = true := by
  rw [value6, value10, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (124 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 9 = true := by
  rw [value9, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(124 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (118 : Vertex) [(124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value12, value13, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 82 = false := by
  rw [value12, value13, value23, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 32 = false ∨ valuation q 82 = false := by
  rw [value12, value13, value32, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (224 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 13 = true ∨ valuation q 23 = true ∨ valuation q 82 = true := by
  rw [value12, value13, value23, value82, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (224 : Vertex) [(161 : Vertex), (176 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 13 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value12, value13, value23, value32, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (416 : Vertex) [(161 : Vertex), (176 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value12, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value12, value13, value14, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 83 = false := by
  rw [value12, value13, value14, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value12, value13, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 83 = false := by
  rw [value12, value13, value15, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 129 = true ∨ valuation q 12 = true ∨ valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 17 = true := by
  rw [value12, value13, value14, value15, value17, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (417 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value13, value14, value16, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (167 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 25 = false := by
  rw [value13, value14, value16, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (167 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 33 = false := by
  rw [value13, value14, value16, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (167 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value13, value14, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value13, value14, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value14, value16, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (167 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 33 = false := by
  rw [value14, value16, value19, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (167 : Vertex) (171 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value14, value16, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (167 : Vertex) (179 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value14, value19, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (171 : Vertex) (179 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 19 = true ∨ valuation q 25 = true ∨ valuation q 33 = true := by
  rw [value13, value14, value19, value25, value33, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (163 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(161 : Vertex), (171 : Vertex), (179 : Vertex), (227 : Vertex)] := by decide
  have hg := other_cover q (163 : Vertex) (167 : Vertex) [(161 : Vertex), (171 : Vertex), (179 : Vertex), (227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 25 = true ∨ valuation q 33 = true := by
  rw [value13, value14, value16, value25, value33, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (163 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(161 : Vertex), (167 : Vertex), (179 : Vertex), (227 : Vertex)] := by decide
  have hg := other_cover q (163 : Vertex) (171 : Vertex) [(161 : Vertex), (167 : Vertex), (179 : Vertex), (227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 35 = true := by
  rw [value13, value15, value16, value20, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ∈ [(161 : Vertex), (167 : Vertex), (173 : Vertex), (229 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (165 : Vertex) [(161 : Vertex), (167 : Vertex), (173 : Vertex), (229 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value13, value15, value16, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (167 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 35 = false := by
  rw [value13, value15, value16, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (167 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 35 = false := by
  rw [value13, value15, value20, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E088.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112088
