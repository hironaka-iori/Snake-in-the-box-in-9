import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value24, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (163 : Vertex) [(177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 14 = true ∨ valuation q 23 = true := by
  rw [value14, value23, value24, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(163 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 14 = true ∨ valuation q 22 = true := by
  rw [value14, value22, value24, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(163 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(163 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 16 = true ∨ valuation q 23 = true ∨ valuation q 29 = true := by
  rw [value16, value23, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ∈ [(166 : Vertex), (178 : Vertex), (190 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (182 : Vertex) [(166 : Vertex), (178 : Vertex), (190 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 23 = true ∨ valuation q 29 = true := by
  rw [value23, value25, value29, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(178 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(178 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 29 = true := by
  rw [value16, value25, value29, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(166 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (178 : Vertex) [(166 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 23 = true := by
  rw [value16, value23, value25, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(166 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (190 : Vertex) [(166 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value17, value21, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (176 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 46 = false := by
  rw [value17, value21, value26, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (176 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 94 = false := by
  rw [value17, value21, value26, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (176 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 46 = false := by
  rw [value17, value26, value27, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 94 = false := by
  rw [value17, value26, value27, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 17 = false ∨ valuation q 46 = false ∨ valuation q 94 = false := by
  rw [value17, value26, value46, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 46 = false := by
  rw [value21, value26, value27, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 94 = false := by
  rw [value21, value26, value27, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 21 = false ∨ valuation q 46 = false ∨ valuation q 94 = false := by
  rw [value21, value26, value46, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 46 = false ∨ valuation q 94 = false := by
  rw [value26, value27, value46, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (188 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 17 = true ∨ valuation q 21 = true ∨ valuation q 46 = true ∨ valuation q 94 = true := by
  rw [value17, value21, value26, value46, value94, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(168 : Vertex), (176 : Vertex), (248 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (188 : Vertex) [(168 : Vertex), (176 : Vertex), (248 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 27 = true := by
  rw [value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (188 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 29 = true := by
  rw [value26, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ∈ [(184 : Vertex), (189 : Vertex), (190 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (188 : Vertex) [(184 : Vertex), (189 : Vertex), (190 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value26, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (184 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 28 = true ∨ valuation q 29 = true := by
  rw [value27, value28, value29, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (184 : Vertex) [(189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 26 = true ∨ valuation q 29 = true := by
  rw [value26, value27, value29, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(184 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(184 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value26, value27, value28, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(184 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(184 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value19, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value27, value28, value30, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 19 = true ∨ valuation q 30 = true := by
  rw [value19, value28, value30, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(173 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (188 : Vertex) [(173 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value25, value27, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value27, value29, value30, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (182 : Vertex) [(188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 25 = true ∨ valuation q 30 = true := by
  rw [value25, value29, value30, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(182 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (188 : Vertex) [(182 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 50 = false ∨ valuation q 98 = false := by
  rw [value20, value30, value50, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (175 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 50 = false := by
  rw [value28, value29, value30, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (190 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E169.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112169
