import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 163 = true ∨ valuation q 39 = true := by
  rw [value39, value40, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(242 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (227 : Vertex) [(242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 163 = true ∨ valuation q 30 = true := by
  rw [value30, value40, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(227 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (242 : Vertex) [(227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 22 = false ∨ valuation q 38 = false ∨ valuation q 44 = false := by
  rw [value22, value38, value41, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (180 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 22 = false ∨ valuation q 44 = false ∨ valuation q 115 = false := by
  rw [value22, value41, value44, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (180 : Vertex) (252 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 38 = false ∨ valuation q 44 = false ∨ valuation q 115 = false := by
  rw [value38, value41, value44, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (240 : Vertex) (252 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 164 = true ∨ valuation q 22 = true ∨ valuation q 38 = true ∨ valuation q 115 = true := by
  rw [value22, value38, value41, value115, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(180 : Vertex), (240 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (252 : Vertex) [(180 : Vertex), (240 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 164 = true ∨ valuation q 22 = true ∨ valuation q 38 = true ∨ valuation q 44 = true := by
  rw [value22, value38, value41, value44, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(180 : Vertex), (240 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (500 : Vertex) [(180 : Vertex), (240 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value34, value38, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (232 : Vertex) (240 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 44 = false := by
  rw [value34, value38, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (232 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 34 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value34, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (232 : Vertex) (250 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value38, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (240 : Vertex) (250 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 165 = true ∨ valuation q 34 = true ∨ valuation q 38 = true ∨ valuation q 43 = true := by
  rw [value34, value38, value42, value43, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(232 : Vertex), (240 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (252 : Vertex) [(232 : Vertex), (240 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 166 = true ∨ valuation q 27 = true ∨ valuation q 42 = true ∨ valuation q 120 = true := by
  rw [value27, value42, value43, value120, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (250 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(186 : Vertex), (248 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (250 : Vertex) (242 : Vertex) [(186 : Vertex), (248 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 167 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value42, value44, value45, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(248 : Vertex), (253 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (244 : Vertex) [(248 : Vertex), (253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 167 = true ∨ valuation q 41 = true ∨ valuation q 45 = true := by
  rw [value41, value44, value45, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(244 : Vertex), (253 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (248 : Vertex) [(244 : Vertex), (253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 167 = true ∨ valuation q 41 = true ∨ valuation q 42 = true := by
  rw [value41, value42, value44, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [(244 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (253 : Vertex) [(244 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 45 = true := by
  rw [value45, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (253 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = true ∨ valuation q 46 = true ∨ valuation q 122 = true := by
  rw [value44, value45, value46, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ∈ [(252 : Vertex), (255 : Vertex), (509 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (253 : Vertex) [(252 : Vertex), (255 : Vertex), (509 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 122 = false := by
  rw [value44, value45, value46, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (252 : Vertex) (255 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 168 = true ∨ valuation q 46 = true ∨ valuation q 122 = true := by
  rw [value45, value46, value122, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(255 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (252 : Vertex) [(255 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 168 = true ∨ valuation q 44 = true ∨ valuation q 122 = true := by
  rw [value44, value45, value122, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(252 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (255 : Vertex) [(252 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 168 = true ∨ valuation q 44 = true ∨ valuation q 46 = true := by
  rw [value44, value45, value46, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(252 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (509 : Vertex) [(252 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 45 = false ∨ valuation q 123 = false := by
  rw [value37, value45, value46, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (239 : Vertex) (253 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 169 = true ∨ valuation q 45 = true ∨ valuation q 123 = true := by
  rw [value45, value46, value123, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(253 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (239 : Vertex) [(253 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 169 = true ∨ valuation q 37 = true ∨ valuation q 123 = true := by
  rw [value37, value46, value123, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [(239 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (253 : Vertex) [(239 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 169 = true ∨ valuation q 37 = true ∨ valuation q 45 = true := by
  rw [value37, value45, value46, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(239 : Vertex), (253 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (511 : Vertex) [(239 : Vertex), (253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 170 = true ∨ valuation q 49 = true ∨ valuation q 52 = true := by
  rw [value47, value49, value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (290 : Vertex) → w ∈ [(292 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (290 : Vertex) [(292 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 170 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value47, value48, value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (292 : Vertex) → w ∈ [(290 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (292 : Vertex) [(290 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 170 = true ∨ valuation q 48 = true ∨ valuation q 49 = true := by
  rw [value47, value48, value49, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(290 : Vertex), (292 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (296 : Vertex) [(290 : Vertex), (292 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value47, value48, value50, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (290 : Vertex) (288 : Vertex) (294 : Vertex) (298 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 171 = true ∨ valuation q 50 = true ∨ valuation q 54 = true := by
  rw [value48, value50, value54, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(294 : Vertex), (298 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (288 : Vertex) [(294 : Vertex), (298 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 171 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value47, value48, value50, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (298 : Vertex) → w ∈ [(288 : Vertex), (294 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (298 : Vertex) [(288 : Vertex), (294 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E097.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112097
