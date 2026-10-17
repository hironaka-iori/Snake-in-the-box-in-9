import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 61 = false ∨ valuation q 70 = false := by
  rw [value54, value60, value61, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 61 = false ∨ valuation q 81 = false := by
  rw [value54, value60, value61, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 54 = false ∨ valuation q 70 = false ∨ valuation q 81 = false := by
  rw [value54, value60, value70, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (152 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 70 = false ∨ valuation q 81 = false := by
  rw [value60, value61, value70, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (152 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 54 = true ∨ valuation q 61 = true ∨ valuation q 70 = true ∨ valuation q 81 = true := by
  rw [value54, value60, value61, value70, value81, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (136 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(128 : Vertex), (137 : Vertex), (152 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (136 : Vertex) (8 : Vertex) [(128 : Vertex), (137 : Vertex), (152 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 5 = true ∨ valuation q 54 = true ∨ valuation q 61 = true ∨ valuation q 81 = true := by
  rw [value5, value54, value60, value61, value81, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (136 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(8 : Vertex), (128 : Vertex), (137 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (136 : Vertex) (152 : Vertex) [(8 : Vertex), (128 : Vertex), (137 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 176 = true ∨ valuation q 5 = true ∨ valuation q 54 = true ∨ valuation q 61 = true ∨ valuation q 70 = true := by
  rw [value5, value54, value60, value61, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (136 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(8 : Vertex), (128 : Vertex), (137 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (136 : Vertex) (168 : Vertex) [(8 : Vertex), (128 : Vertex), (137 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value6, value55, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (129 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 55 = false ∨ valuation q 62 = false := by
  rw [value6, value55, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (129 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value6, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (136 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 60 = false ∨ valuation q 63 = false := by
  rw [value6, value60, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (136 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 6 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value6, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (9 : Vertex) (139 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value55, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (136 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 63 = false := by
  rw [value55, value60, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (136 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 55 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value55, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (139 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value60, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (136 : Vertex) (139 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 177 = true ∨ valuation q 55 = true ∨ valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 63 = true := by
  rw [value55, value60, value61, value62, value63, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(129 : Vertex), (136 : Vertex), (139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (9 : Vertex) [(129 : Vertex), (136 : Vertex), (139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 71 = false := by
  rw [value56, value61, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 83 = false := by
  rw [value56, value61, value62, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 61 = true ∨ valuation q 71 = true ∨ valuation q 83 = true := by
  rw [value61, value62, value71, value83, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(137 : Vertex), (155 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (131 : Vertex) [(137 : Vertex), (155 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 56 = true ∨ valuation q 71 = true ∨ valuation q 83 = true := by
  rw [value56, value62, value71, value83, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex), (155 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (137 : Vertex) [(131 : Vertex), (155 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 56 = true ∨ valuation q 61 = true ∨ valuation q 83 = true := by
  rw [value56, value61, value62, value83, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(131 : Vertex), (137 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (155 : Vertex) [(131 : Vertex), (137 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 178 = true ∨ valuation q 56 = true ∨ valuation q 61 = true ∨ valuation q 71 = true := by
  rw [value56, value61, value62, value71, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(131 : Vertex), (137 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (171 : Vertex) [(131 : Vertex), (137 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 8 = false ∨ valuation q 58 = false ∨ valuation q 72 = false := by
  rw [value8, value58, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 72 = false := by
  rw [value58, value61, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 179 = true ∨ valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 72 = true := by
  rw [value58, value61, value63, value72, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(133 : Vertex), (137 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (13 : Vertex) [(133 : Vertex), (137 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 59 = true ∨ valuation q 73 = true := by
  rw [value59, value64, value73, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (14 : Vertex) → w ∈ [(134 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (14 : Vertex) [(134 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 9 = true ∨ valuation q 73 = true := by
  rw [value9, value64, value73, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(14 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (134 : Vertex) [(14 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 180 = true ∨ valuation q 9 = true ∨ valuation q 59 = true := by
  rw [value9, value59, value64, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(14 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (158 : Vertex) [(14 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 11 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value11, value65, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (147 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 11 = false ∨ valuation q 69 = false ∨ valuation q 88 = false := by
  rw [value11, value65, value69, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (150 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 88 = false := by
  rw [value65, value66, value69, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (147 : Vertex) (150 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E259.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112259
