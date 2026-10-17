import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 70 = false := by
  rw [value61, value62, value64, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (290 : Vertex) (299 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 82 = false := by
  rw [value61, value62, value64, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (290 : Vertex) (299 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 64 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value62, value64, value70, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (299 : Vertex) (307 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 4 = false ∨ valuation q 60 = false ∨ valuation q 83 = false := by
  rw [value4, value60, value63, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (37 : Vertex) (289 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 60 = false ∨ valuation q 65 = false ∨ valuation q 83 = false := by
  rw [value60, value63, value65, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (301 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 170 = true ∨ valuation q 6 = true ∨ valuation q 62 = true ∨ valuation q 66 = true := by
  rw [value6, value62, value64, value66, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(43 : Vertex), (291 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (363 : Vertex) [(43 : Vertex), (291 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 171 = true ∨ valuation q 66 = true ∨ valuation q 74 = true := by
  rw [value65, value66, value74, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(303 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (293 : Vertex) [(303 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 76 = false := by
  rw [value64, value65, value66, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 9 = false ∨ valuation q 59 = false ∨ valuation q 69 = false := by
  rw [value9, value59, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (48 : Vertex) (288 : Vertex) (306 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 9 = false ∨ valuation q 59 = false ∨ valuation q 85 = false := by
  rw [value9, value59, value67, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (48 : Vertex) (288 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 9 = false ∨ valuation q 69 = false ∨ valuation q 85 = false := by
  rw [value9, value67, value69, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (48 : Vertex) (306 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 59 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value59, value67, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (288 : Vertex) (306 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 85 = false := by
  rw [value67, value68, value69, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (305 : Vertex) (306 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 85 = false := by
  rw [value67, value68, value72, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (305 : Vertex) (312 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 85 = false := by
  rw [value67, value69, value72, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (306 : Vertex) (312 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 60 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value60, value67, value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value61, value67, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (290 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value61, value67, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (290 : Vertex) (304 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 61 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value61, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (290 : Vertex) (307 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value67, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (304 : Vertex) (307 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 176 = true ∨ valuation q 68 = true ∨ valuation q 69 = true := by
  rw [value68, value69, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (291 : Vertex) → w ∈ [(305 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (291 : Vertex) [(305 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 176 = true ∨ valuation q 62 = true ∨ valuation q 69 = true := by
  rw [value62, value69, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(291 : Vertex), (306 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(291 : Vertex), (306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 176 = true ∨ valuation q 62 = true ∨ valuation q 68 = true := by
  rw [value62, value68, value70, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(291 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (306 : Vertex) [(291 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 177 = true ∨ valuation q 75 = true := by
  rw [value71, value75, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(318 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (306 : Vertex) [(318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 177 = true ∨ valuation q 69 = true := by
  rw [value69, value71, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(306 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 13 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value13, value67, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (312 : Vertex) (56 : Vertex) (304 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 75 = true := by
  rw [value72, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ∈ [(312 : Vertex), (317 : Vertex), (318 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (316 : Vertex) [(312 : Vertex), (317 : Vertex), (318 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 179 = true ∨ valuation q 74 = true ∨ valuation q 75 = true := by
  rw [value73, value74, value75, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (312 : Vertex) → w ∈ [(317 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (312 : Vertex) [(317 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 179 = true ∨ valuation q 72 = true ∨ valuation q 74 = true := by
  rw [value72, value73, value74, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(312 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (318 : Vertex) [(312 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 65 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value65, value73, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (301 : Vertex) (316 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 71 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value71, value73, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (318 : Vertex) (310 : Vertex) (316 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 16 = false ∨ valuation q 66 = false ∨ valuation q 74 = false := by
  rw [value16, value66, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (63 : Vertex) (303 : Vertex) (317 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E246.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112246
