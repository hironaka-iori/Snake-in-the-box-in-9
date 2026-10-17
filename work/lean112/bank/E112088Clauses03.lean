import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 41 = false := by
  rw [value14, value17, value19, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (163 : Vertex) (169 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 22 = true ∨ valuation q 41 = true := by
  rw [value17, value18, value19, value22, value41, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(169 : Vertex), (170 : Vertex), (175 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (163 : Vertex) [(169 : Vertex), (170 : Vertex), (175 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 22 = true ∨ valuation q 41 = true := by
  rw [value14, value18, value19, value22, value41, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(163 : Vertex), (170 : Vertex), (175 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (169 : Vertex) [(163 : Vertex), (170 : Vertex), (175 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 22 = true ∨ valuation q 41 = true := by
  rw [value14, value17, value19, value22, value41, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(163 : Vertex), (169 : Vertex), (175 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (170 : Vertex) [(163 : Vertex), (169 : Vertex), (175 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 41 = true := by
  rw [value14, value17, value18, value19, value41, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex), (169 : Vertex), (170 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (175 : Vertex) [(163 : Vertex), (169 : Vertex), (170 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 22 = true := by
  rw [value14, value17, value18, value19, value22, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(163 : Vertex), (169 : Vertex), (170 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (235 : Vertex) [(163 : Vertex), (169 : Vertex), (170 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 30 = false := by
  rw [value15, value17, value20, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (169 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value15, value20, value22, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value17, value20, value22, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (169 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 17 = true ∨ valuation q 22 = true ∨ valuation q 30 = true := by
  rw [value17, value20, value22, value30, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(169 : Vertex), (175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (165 : Vertex) [(169 : Vertex), (175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 22 = true ∨ valuation q 30 = true := by
  rw [value15, value20, value22, value30, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(165 : Vertex), (175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (169 : Vertex) [(165 : Vertex), (175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 30 = true := by
  rw [value15, value17, value20, value30, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(165 : Vertex), (169 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(165 : Vertex), (169 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 22 = true := by
  rw [value15, value17, value20, value22, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(165 : Vertex), (169 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(165 : Vertex), (169 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 18 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value18, value21, value31, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (170 : Vertex) (190 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 18 = false ∨ valuation q 31 = false ∨ valuation q 89 = false := by
  rw [value18, value21, value31, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (170 : Vertex) (190 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 31 = false ∨ valuation q 43 = false := by
  rw [value21, value22, value31, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (175 : Vertex) (190 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 31 = false ∨ valuation q 89 = false := by
  rw [value21, value22, value31, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (175 : Vertex) (190 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value16, value19, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (171 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 21 = false := by
  rw [value16, value19, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (171 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 90 = false := by
  rw [value16, value19, value22, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (171 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 16 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value16, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (173 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 90 = false := by
  rw [value16, value21, value22, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (174 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value19, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (173 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 90 = false := by
  rw [value20, value21, value22, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (173 : Vertex) (174 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 90 = true := by
  rw [value19, value20, value21, value22, value90, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(171 : Vertex), (173 : Vertex), (174 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (167 : Vertex) [(171 : Vertex), (173 : Vertex), (174 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 90 = true := by
  rw [value16, value20, value21, value22, value90, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(167 : Vertex), (173 : Vertex), (174 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (171 : Vertex) [(167 : Vertex), (173 : Vertex), (174 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 12 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value12, value23, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 24 = true ∨ valuation q 26 = true := by
  rw [value23, value24, value26, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(178 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (160 : Vertex) [(178 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 12 = true ∨ valuation q 26 = true := by
  rw [value12, value23, value26, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(160 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (178 : Vertex) [(160 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true ∨ valuation q 12 = true ∨ valuation q 24 = true := by
  rw [value12, value23, value24, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(160 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (180 : Vertex) [(160 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value23, value24, value25, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 23 = false ∨ valuation q 27 = false := by
  rw [value23, value27, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (178 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E088.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112088
