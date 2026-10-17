import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 35 = false ∨ valuation q 54 = false := by
  rw [value13, value18, value35, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (87 : Vertex) (127 : Vertex) (223 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 35 = true ∨ valuation q 54 = true ∨ valuation q 92 = true := by
  rw [value13, value16, value17, value18, value35, value54, value92, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(87 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (223 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (79 : Vertex) [(87 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (223 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 9 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 35 = true ∨ valuation q 54 = true ∨ valuation q 92 = true := by
  rw [value9, value16, value17, value18, value35, value54, value92, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(79 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (223 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (87 : Vertex) [(79 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (223 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 9 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 35 = true ∨ valuation q 92 = true := by
  rw [value9, value13, value16, value17, value18, value35, value92, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (223 : Vertex) → w ∈ [(79 : Vertex), (87 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (351 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (223 : Vertex) [(79 : Vertex), (87 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (351 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 9 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 35 = true ∨ valuation q 54 = true := by
  rw [value9, value13, value16, value17, value18, value35, value54, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(79 : Vertex), (87 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (351 : Vertex) [(79 : Vertex), (87 : Vertex), (93 : Vertex), (94 : Vertex), (127 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 19 = true := by
  rw [value19, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (96 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = true ∨ valuation q 27 = true ∨ valuation q 55 = true := by
  rw [value19, value20, value27, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ∈ [(98 : Vertex), (112 : Vertex), (224 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (96 : Vertex) [(98 : Vertex), (112 : Vertex), (224 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 27 = false ∨ valuation q 55 = false := by
  rw [value19, value20, value27, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (98 : Vertex) (112 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 20 = false ∨ valuation q 55 = false := by
  rw [value20, value55, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (96 : Vertex) (98 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 27 = true ∨ valuation q 55 = true := by
  rw [value19, value27, value55, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (98 : Vertex) → w ∈ [(112 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (98 : Vertex) [(112 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 55 = true := by
  rw [value19, value20, value55, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (112 : Vertex) → w ∈ [(98 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (112 : Vertex) [(98 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 27 = true := by
  rw [value19, value20, value27, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(98 : Vertex), (112 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (224 : Vertex) [(98 : Vertex), (112 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 19 = true := by
  rw [value19, value20, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [(96 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (66 : Vertex) [(96 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 2 = true := by
  rw [value2, value20, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(66 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (96 : Vertex) [(66 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 21 = true := by
  rw [value21, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (101 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 3 = true ∨ valuation q 22 = true := by
  rw [value3, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex), (103 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (101 : Vertex) [(69 : Vertex), (103 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 3 = false ∨ valuation q 22 = false := by
  rw [value3, value22, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (101 : Vertex) (69 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 148 = true ∨ valuation q 22 = true := by
  rw [value21, value22, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(103 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (69 : Vertex) [(103 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 148 = true ∨ valuation q 3 = true := by
  rw [value3, value21, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (101 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(69 : Vertex)] := by decide
  have hg := other_cover q (101 : Vertex) (103 : Vertex) [(69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 149 = true ∨ valuation q 58 = true := by
  rw [value22, value58, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(231 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (101 : Vertex) [(231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 149 = true ∨ valuation q 21 = true := by
  rw [value21, value22, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(101 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (231 : Vertex) [(101 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 23 = true := by
  rw [value23, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (105 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = true ∨ valuation q 24 = true := by
  rw [value6, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ∈ [(73 : Vertex), (107 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (105 : Vertex) [(73 : Vertex), (107 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 150 = true ∨ valuation q 24 = true := by
  rw [value23, value24, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(107 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (73 : Vertex) [(107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 150 = true ∨ valuation q 6 = true := by
  rw [value6, value23, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(73 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (107 : Vertex) [(73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 60 = false := by
  rw [value7, value23, value24, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (75 : Vertex) (105 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 23 = true ∨ valuation q 60 = true := by
  rw [value23, value24, value60, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(105 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (75 : Vertex) [(105 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 7 = true ∨ valuation q 60 = true := by
  rw [value7, value24, value60, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(75 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (105 : Vertex) [(75 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 151 = true ∨ valuation q 7 = true ∨ valuation q 23 = true := by
  rw [value7, value23, value24, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(75 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (235 : Vertex) [(75 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 25 = true := by
  rw [value25, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (108 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 8 = true ∨ valuation q 26 = true := by
  rw [value8, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ∈ [(76 : Vertex), (110 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (108 : Vertex) [(76 : Vertex), (110 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 8 = false ∨ valuation q 26 = false := by
  rw [value8, value26, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (108 : Vertex) (76 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E256.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112256
