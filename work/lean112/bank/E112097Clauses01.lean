import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 137 = true ∨ valuation q 13 = true := by
  rw [value13, value14, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(160 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (170 : Vertex) [(160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value13, value15, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (160 : Vertex) (172 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 138 = true ∨ valuation q 13 = true ∨ valuation q 22 = true := by
  rw [value13, value15, value22, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(160 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (172 : Vertex) [(160 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 6 = false ∨ valuation q 25 = false ∨ valuation q 33 = false := by
  rw [value6, value16, value25, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (39 : Vertex) (183 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 139 = true ∨ valuation q 25 = true ∨ valuation q 33 = true := by
  rw [value16, value25, value33, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(183 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (39 : Vertex) [(183 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 20 = false := by
  rw [value7, value13, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (160 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 7 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value7, value17, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 7 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value7, value17, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (172 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 7 = false ∨ valuation q 20 = false ∨ valuation q 86 = false := by
  rw [value7, value17, value20, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (172 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value13, value17, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (170 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value13, value17, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (172 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 13 = false ∨ valuation q 20 = false ∨ valuation q 86 = false := by
  rw [value13, value17, value20, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (172 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value17, value18, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (170 : Vertex) (172 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 86 = false := by
  rw [value17, value18, value20, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (170 : Vertex) (172 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 86 = false := by
  rw [value17, value20, value34, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (172 : Vertex) (232 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value14, value18, value19, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (162 : Vertex) (171 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 141 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 27 = true := by
  rw [value17, value18, value19, value27, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(168 : Vertex), (171 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (162 : Vertex) [(168 : Vertex), (171 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 27 = true := by
  rw [value14, value17, value18, value27, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(162 : Vertex), (168 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (171 : Vertex) [(162 : Vertex), (168 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 19 = true := by
  rw [value14, value17, value18, value19, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(162 : Vertex), (168 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (186 : Vertex) [(162 : Vertex), (168 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 87 = false := by
  rw [value18, value19, value28, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (170 : Vertex) (187 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 142 = true ∨ valuation q 28 = true ∨ valuation q 87 = true := by
  rw [value19, value28, value87, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(187 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (170 : Vertex) [(187 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 88 = true := by
  rw [value15, value17, value20, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ∈ [(164 : Vertex), (168 : Vertex), (428 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (172 : Vertex) [(164 : Vertex), (168 : Vertex), (428 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 15 = false ∨ valuation q 88 = false := by
  rw [value15, value88, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (172 : Vertex) (164 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 17 = false ∨ valuation q 88 = false := by
  rw [value17, value88, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (172 : Vertex) (168 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 20 = true := by
  rw [value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 143 = true := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 92 = false := by
  rw [value21, value23, value26, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (181 : Vertex) (185 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 144 = true ∨ valuation q 26 = true ∨ valuation q 92 = true := by
  rw [value21, value26, value92, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(185 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (181 : Vertex) [(185 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 92 = true := by
  rw [value21, value23, value92, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(181 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (185 : Vertex) [(181 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value21, value23, value26, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(181 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (433 : Vertex) [(181 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 23 = false := by
  rw [value11, value15, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (164 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 24 = false := by
  rw [value11, value15, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (164 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E097.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112097
