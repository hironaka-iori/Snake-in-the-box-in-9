import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 25 = true ∨ valuation q 27 = true := by
  rw [value24, value25, value27, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(179 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (176 : Vertex) [(179 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 27 = true := by
  rw [value23, value24, value27, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(176 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (179 : Vertex) [(176 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 25 = true := by
  rw [value23, value24, value25, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(176 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (182 : Vertex) [(176 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 24 = true ∨ valuation q 44 = true ∨ valuation q 91 = true := by
  rw [value24, value25, value44, value91, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(178 : Vertex), (243 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (163 : Vertex) [(178 : Vertex), (243 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 24 = true ∨ valuation q 91 = true := by
  rw [value14, value24, value25, value91, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (243 : Vertex) [(163 : Vertex), (178 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 14 = true ∨ valuation q 24 = true ∨ valuation q 44 = true := by
  rw [value14, value24, value25, value44, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (435 : Vertex) [(163 : Vertex), (178 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value23, value26, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 27 = false ∨ valuation q 45 = false := by
  rw [value23, value26, value27, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (182 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 27 = false ∨ valuation q 92 = false := by
  rw [value23, value26, value27, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (182 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 45 = false := by
  rw [value23, value26, value29, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (188 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 92 = false := by
  rw [value23, value26, value29, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (188 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 45 = false ∨ valuation q 92 = false := by
  rw [value23, value26, value45, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 45 = false := by
  rw [value26, value27, value29, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 92 = false := by
  rw [value26, value27, value29, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 45 = false ∨ valuation q 92 = false := by
  rw [value26, value27, value45, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 29 = false ∨ valuation q 45 = false ∨ valuation q 92 = false := by
  rw [value26, value29, value45, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (188 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 142 = true ∨ valuation q 23 = true ∨ valuation q 29 = true ∨ valuation q 45 = true ∨ valuation q 92 = true := by
  rw [value23, value26, value29, value45, value92, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(176 : Vertex), (188 : Vertex), (244 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (182 : Vertex) [(176 : Vertex), (188 : Vertex), (244 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 26 = true ∨ valuation q 31 = true := by
  rw [value26, value27, value31, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(180 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (178 : Vertex) [(180 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 24 = true ∨ valuation q 31 = true := by
  rw [value24, value27, value31, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(178 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (180 : Vertex) [(178 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 143 = true ∨ valuation q 24 = true ∨ valuation q 26 = true := by
  rw [value24, value26, value27, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(178 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (190 : Vertex) [(178 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 17 = false ∨ valuation q 30 = false ∨ valuation q 49 = false := by
  rw [value17, value28, value30, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (189 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 30 = true ∨ valuation q 49 = true := by
  rw [value28, value30, value49, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(189 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (169 : Vertex) [(189 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 17 = true ∨ valuation q 49 = true := by
  rw [value17, value28, value49, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(169 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (189 : Vertex) [(169 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 144 = true ∨ valuation q 17 = true ∨ valuation q 30 = true := by
  rw [value17, value28, value30, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(169 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (249 : Vertex) [(169 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value26, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (180 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value29, value30, value31, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (180 : Vertex) [(189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 26 = true ∨ valuation q 31 = true := by
  rw [value26, value29, value31, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(180 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(180 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 26 = true ∨ valuation q 30 = true := by
  rw [value26, value29, value30, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(180 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(180 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value20, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 20 = false ∨ valuation q 29 = false := by
  rw [value20, value29, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value28, value29, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (189 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 28 = true ∨ valuation q 29 = true := by
  rw [value28, value29, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(185 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(185 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E088.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112088
