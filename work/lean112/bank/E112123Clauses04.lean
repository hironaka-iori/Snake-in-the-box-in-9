import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 143 = true ∨ valuation q 35 = true ∨ valuation q 40 = true := by
  rw [value33, value35, value40, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(162 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(162 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 143 = true ∨ valuation q 34 = true ∨ valuation q 35 = true := by
  rw [value33, value34, value35, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(161 : Vertex), (162 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (176 : Vertex) [(161 : Vertex), (162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value33, value34, value36, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 33 = false ∨ valuation q 42 = false ∨ valuation q 50 = false := by
  rw [value33, value35, value42, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 52 = false := by
  rw [value34, value36, value38, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 147 = true ∨ valuation q 39 = true := by
  rw [value37, value39, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(175 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (427 : Vertex) [(175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 148 = true ∨ valuation q 39 = true ∨ valuation q 47 = true := by
  rw [value38, value39, value47, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (165 : Vertex) [(175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 148 = true ∨ valuation q 36 = true ∨ valuation q 39 = true := by
  rw [value36, value38, value39, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(165 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(165 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 49 = false := by
  rw [value37, value38, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (173 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 33 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value33, value40, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 33 = false ∨ valuation q 41 = false ∨ valuation q 88 = false := by
  rw [value33, value40, value41, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 33 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value33, value40, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 33 = false ∨ valuation q 42 = false ∨ valuation q 88 = false := by
  rw [value33, value40, value42, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 33 = false ∨ valuation q 45 = false ∨ valuation q 88 = false := by
  rw [value33, value40, value45, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (184 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value40, value41, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 151 = true ∨ valuation q 34 = true ∨ valuation q 40 = true := by
  rw [value34, value40, value41, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (179 : Vertex) [(161 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 155 = true ∨ valuation q 40 = true ∨ valuation q 46 = true := by
  rw [value40, value45, value46, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(176 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (248 : Vertex) [(176 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value45, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (184 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value38, value46, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 35 = false ∨ valuation q 53 = false := by
  rw [value35, value53, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (226 : Vertex) (162 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 50 = true := by
  rw [value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 160 = true := by
  rw [value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 165 = true ∨ valuation q 53 = true := by
  rw [value53, value55, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(234 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (236 : Vertex) [(234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 45 = false ∨ valuation q 60 = false := by
  rw [value45, value60, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (248 : Vertex) (184 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 169 = true ∨ valuation q 45 = true := by
  rw [value45, value59, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(184 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 170 = true ∨ valuation q 59 = true := by
  rw [value59, value60, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(248 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (251 : Vertex) [(248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 3 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value3, value63, value64, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (2 : Vertex) (259 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 173 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value63, value64, value67, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(259 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (2 : Vertex) [(259 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 173 = true ∨ valuation q 3 = true ∨ valuation q 67 = true := by
  rw [value3, value63, value67, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(2 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (259 : Vertex) [(2 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 173 = true ∨ valuation q 3 = true ∨ valuation q 64 = true := by
  rw [value3, value63, value64, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(2 : Vertex), (259 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(2 : Vertex), (259 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 4 = false ∨ valuation q 63 = false ∨ valuation q 81 = false := by
  rw [value4, value63, value64, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (3 : Vertex) (258 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 4 = false ∨ valuation q 68 = false ∨ valuation q 81 = false := by
  rw [value4, value64, value68, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (3 : Vertex) (267 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E123.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112123
