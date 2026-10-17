import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 139 = true ∨ valuation q 27 = true ∨ valuation q 88 = true := by
  rw [value18, value27, value88, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(184 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (160 : Vertex) [(184 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 139 = true ∨ valuation q 12 = true ∨ valuation q 88 = true := by
  rw [value12, value18, value88, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(160 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (184 : Vertex) [(160 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 139 = true ∨ valuation q 12 = true ∨ valuation q 27 = true := by
  rw [value12, value18, value27, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(160 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (424 : Vertex) [(160 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 21 = false ∨ valuation q 90 = false := by
  rw [value15, value19, value21, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (163 : Vertex) (175 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 38 = false ∨ valuation q 90 = false := by
  rw [value19, value21, value38, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (175 : Vertex) (235 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 140 = true ∨ valuation q 21 = true ∨ valuation q 38 = true ∨ valuation q 90 = true := by
  rw [value19, value21, value38, value90, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(175 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (163 : Vertex) [(175 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 140 = true ∨ valuation q 15 = true ∨ valuation q 38 = true ∨ valuation q 90 = true := by
  rw [value15, value19, value38, value90, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (175 : Vertex) [(163 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 140 = true ∨ valuation q 15 = true ∨ valuation q 21 = true ∨ valuation q 90 = true := by
  rw [value15, value19, value21, value90, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (235 : Vertex) [(163 : Vertex), (175 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 140 = true ∨ valuation q 15 = true ∨ valuation q 21 = true ∨ valuation q 38 = true := by
  rw [value15, value19, value21, value38, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (427 : Vertex) [(163 : Vertex), (175 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 29 = false := by
  rw [value16, value20, value21, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 141 = true ∨ valuation q 21 = true ∨ valuation q 29 = true := by
  rw [value20, value21, value29, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (165 : Vertex) [(175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 29 = true := by
  rw [value16, value20, value29, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(165 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(165 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 21 = true := by
  rw [value16, value20, value21, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(165 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(165 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 31 = false := by
  rw [value19, value20, value21, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (173 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 93 = false := by
  rw [value19, value20, value21, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (173 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 19 = false ∨ valuation q 31 = false ∨ valuation q 93 = false := by
  rw [value19, value21, value31, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (191 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 20 = false ∨ valuation q 31 = false ∨ valuation q 93 = false := by
  rw [value20, value21, value31, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (173 : Vertex) (191 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 142 = true ∨ valuation q 20 = true ∨ valuation q 31 = true ∨ valuation q 93 = true := by
  rw [value20, value21, value31, value93, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(173 : Vertex), (191 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (171 : Vertex) [(173 : Vertex), (191 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 142 = true ∨ valuation q 19 = true ∨ valuation q 31 = true ∨ valuation q 93 = true := by
  rw [value19, value21, value31, value93, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(171 : Vertex), (191 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [(171 : Vertex), (191 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 12 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value12, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 12 = false ∨ valuation q 23 = false ∨ valuation q 27 = false := by
  rw [value12, value22, value23, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 12 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value12, value22, value24, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value22, value23, value24, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 143 = true ∨ valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 27 = true := by
  rw [value22, value23, value24, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(177 : Vertex), (178 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (160 : Vertex) [(177 : Vertex), (178 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 143 = true ∨ valuation q 12 = true ∨ valuation q 24 = true ∨ valuation q 27 = true := by
  rw [value12, value22, value24, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (178 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (177 : Vertex) [(160 : Vertex), (178 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 143 = true ∨ valuation q 12 = true ∨ valuation q 23 = true ∨ valuation q 27 = true := by
  rw [value12, value22, value23, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(160 : Vertex), (177 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (178 : Vertex) [(160 : Vertex), (177 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 143 = true ∨ valuation q 12 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value12, value22, value23, value24, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(160 : Vertex), (177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (184 : Vertex) [(160 : Vertex), (177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value13, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 94 = false := by
  rw [value13, value22, value23, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 94 = false := by
  rw [value13, value23, value25, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (179 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 94 = false := by
  rw [value22, value23, value25, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (176 : Vertex) (179 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 144 = true ∨ valuation q 13 = true ∨ valuation q 25 = true ∨ valuation q 94 = true := by
  rw [value13, value23, value25, value94, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(161 : Vertex), (179 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (176 : Vertex) [(161 : Vertex), (179 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E024.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112024
