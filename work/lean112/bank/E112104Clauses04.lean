import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 14 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value14, value32, value36, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (100 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 99 = false := by
  rw [value32, value36, value41, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (236 : Vertex) (244 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value36, value41, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (228 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 31 = false ∨ valuation q 101 = false := by
  rw [value31, value101, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (231 : Vertex) (227 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 151 = true ∨ valuation q 101 = true := by
  rw [value33, value101, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(487 : Vertex)] := by decide
  have hg := other_cover q (231 : Vertex) (227 : Vertex) [(487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 37 = true ∨ valuation q 103 = true := by
  rw [value34, value37, value103, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(237 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (225 : Vertex) [(237 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 30 = true ∨ valuation q 103 = true := by
  rw [value30, value34, value103, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(225 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (237 : Vertex) [(225 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 30 = true ∨ valuation q 37 = true := by
  rw [value30, value34, value37, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(225 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (489 : Vertex) [(225 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 18 = false ∨ valuation q 42 = false ∨ valuation q 104 = false := by
  rw [value18, value35, value42, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (106 : Vertex) (250 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 42 = true ∨ valuation q 104 = true := by
  rw [value35, value42, value104, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(250 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (106 : Vertex) [(250 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 18 = true ∨ valuation q 104 = true := by
  rw [value18, value35, value104, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(106 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (250 : Vertex) [(106 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 18 = true ∨ valuation q 42 = true := by
  rw [value18, value35, value42, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(106 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (490 : Vertex) [(106 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 32 = true ∨ valuation q 37 = true ∨ valuation q 43 = true ∨ valuation q 106 = true := by
  rw [value32, value36, value37, value43, value106, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(228 : Vertex), (237 : Vertex), (252 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (108 : Vertex) [(228 : Vertex), (237 : Vertex), (252 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 20 = true ∨ valuation q 37 = true ∨ valuation q 43 = true ∨ valuation q 106 = true := by
  rw [value20, value36, value37, value43, value106, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(108 : Vertex), (237 : Vertex), (252 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(108 : Vertex), (237 : Vertex), (252 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 20 = true ∨ valuation q 32 = true ∨ valuation q 43 = true ∨ valuation q 106 = true := by
  rw [value20, value32, value36, value43, value106, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(108 : Vertex), (228 : Vertex), (252 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (237 : Vertex) [(108 : Vertex), (228 : Vertex), (252 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 154 = true ∨ valuation q 20 = true ∨ valuation q 32 = true ∨ valuation q 37 = true ∨ valuation q 106 = true := by
  rw [value20, value32, value36, value37, value106, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(108 : Vertex), (228 : Vertex), (237 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (252 : Vertex) [(108 : Vertex), (228 : Vertex), (237 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 44 = false := by
  rw [value34, value36, value37, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (233 : Vertex) (236 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 107 = false := by
  rw [value34, value36, value37, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (233 : Vertex) (236 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 44 = false ∨ valuation q 107 = false := by
  rw [value34, value37, value44, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (233 : Vertex) (253 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 44 = false ∨ valuation q 107 = false := by
  rw [value36, value37, value44, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (236 : Vertex) (253 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 36 = false ∨ valuation q 107 = false := by
  rw [value36, value107, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (237 : Vertex) (236 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 36 = true ∨ valuation q 44 = true ∨ valuation q 107 = true := by
  rw [value36, value37, value44, value107, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(236 : Vertex), (253 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (233 : Vertex) [(236 : Vertex), (253 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value38, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (241 : Vertex) (242 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value39, value41, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (240 : Vertex) (241 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 30 = true ∨ valuation q 38 = true := by
  rw [value30, value38, value39, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(225 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (113 : Vertex) [(225 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 22 = true ∨ valuation q 38 = true := by
  rw [value22, value38, value39, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(113 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (225 : Vertex) [(113 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 22 = true ∨ valuation q 30 = true := by
  rw [value22, value30, value39, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(113 : Vertex), (225 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (240 : Vertex) [(113 : Vertex), (225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 42 = true := by
  rw [value40, value42, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(250 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (240 : Vertex) [(250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 38 = true := by
  rw [value38, value40, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(240 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (250 : Vertex) [(240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 32 = false ∨ valuation q 38 = false := by
  rw [value32, value38, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (244 : Vertex) (228 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 32 = false ∨ valuation q 43 = false := by
  rw [value32, value43, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (244 : Vertex) (228 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 32 = false ∨ valuation q 110 = false := by
  rw [value32, value110, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (244 : Vertex) (228 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E104.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112104
