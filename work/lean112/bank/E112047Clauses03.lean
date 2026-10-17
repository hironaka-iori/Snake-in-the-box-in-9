import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 36 = false ∨ valuation q 84 = false := by
  rw [value17, value19, value36, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 17 = true ∨ valuation q 36 = true ∨ valuation q 84 = true := by
  rw [value17, value19, value36, value84, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(131 : Vertex), (199 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (143 : Vertex) [(131 : Vertex), (199 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 38 = true ∨ valuation q 86 = true := by
  rw [value15, value20, value38, value86, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(129 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (141 : Vertex) [(129 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 22 = true ∨ valuation q 86 = true := by
  rw [value15, value20, value22, value86, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (201 : Vertex) [(129 : Vertex), (141 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 22 = true ∨ valuation q 38 = true := by
  rw [value15, value20, value22, value38, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(129 : Vertex), (141 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 21 = true := by
  rw [value21, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (138 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 16 = true ∨ valuation q 29 = true ∨ valuation q 87 = true := by
  rw [value16, value21, value29, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ∈ [(130 : Vertex), (154 : Vertex), (394 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (138 : Vertex) [(130 : Vertex), (154 : Vertex), (394 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 16 = false ∨ valuation q 29 = false ∨ valuation q 87 = false := by
  rw [value16, value21, value29, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (130 : Vertex) (154 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 16 = false ∨ valuation q 29 = false := by
  rw [value16, value29, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (138 : Vertex) (130 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 29 = false ∨ valuation q 87 = false := by
  rw [value29, value87, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (138 : Vertex) (154 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 29 = true ∨ valuation q 87 = true := by
  rw [value21, value29, value87, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(154 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (130 : Vertex) [(154 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 16 = true ∨ valuation q 87 = true := by
  rw [value16, value21, value87, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(130 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (154 : Vertex) [(130 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 16 = true ∨ valuation q 29 = true := by
  rw [value16, value21, value29, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(130 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (394 : Vertex) [(130 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 140 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (137 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 140 = true ∨ valuation q 20 = true := by
  rw [value20, value22, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(137 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (143 : Vertex) [(137 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value19, value22, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ∈ [(135 : Vertex), (141 : Vertex), (159 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (143 : Vertex) [(135 : Vertex), (141 : Vertex), (159 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 32 = false := by
  rw [value19, value22, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (135 : Vertex) (141 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 22 = true ∨ valuation q 32 = true := by
  rw [value22, value23, value32, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(141 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (135 : Vertex) [(141 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 32 = true := by
  rw [value19, value23, value32, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(135 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (141 : Vertex) [(135 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 22 = true := by
  rw [value19, value22, value23, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(135 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (159 : Vertex) [(135 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value14, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (145 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value14, value24, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (145 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value14, value24, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (146 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value24, value25, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (145 : Vertex) (146 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value24, value25, value26, value28, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(145 : Vertex), (146 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (128 : Vertex) [(145 : Vertex), (146 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 14 = true ∨ valuation q 25 = true ∨ valuation q 26 = true := by
  rw [value14, value24, value25, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(128 : Vertex), (145 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (148 : Vertex) [(128 : Vertex), (145 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 25 = true := by
  rw [value25, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (145 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 90 = true := by
  rw [value15, value24, value25, value27, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ∈ [(129 : Vertex), (144 : Vertex), (147 : Vertex), (401 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (145 : Vertex) [(129 : Vertex), (144 : Vertex), (147 : Vertex), (401 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 90 = true := by
  rw [value24, value25, value27, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(144 : Vertex), (147 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (129 : Vertex) [(144 : Vertex), (147 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 15 = true ∨ valuation q 27 = true ∨ valuation q 90 = true := by
  rw [value15, value25, value27, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(129 : Vertex), (147 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (144 : Vertex) [(129 : Vertex), (147 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 15 = true ∨ valuation q 24 = true ∨ valuation q 90 = true := by
  rw [value15, value24, value25, value90, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(129 : Vertex), (144 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (147 : Vertex) [(129 : Vertex), (144 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 15 = true ∨ valuation q 24 = true ∨ valuation q 27 = true := by
  rw [value15, value24, value25, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(129 : Vertex), (144 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (401 : Vertex) [(129 : Vertex), (144 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E047.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112047
