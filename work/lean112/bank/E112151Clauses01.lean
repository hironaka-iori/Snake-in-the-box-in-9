import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 129 = true ∨ valuation q 18 = true ∨ valuation q 91 = true := by
  rw [value18, value22, value91, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(179 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (186 : Vertex) [(179 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 92 = false := by
  rw [value14, value23, value24, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (172 : Vertex) (189 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 131 = true ∨ valuation q 19 = true ∨ valuation q 23 = true := by
  rw [value19, value23, value24, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(181 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(181 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 131 = true ∨ valuation q 15 = true ∨ valuation q 19 = true := by
  rw [value15, value19, value24, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(173 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (188 : Vertex) [(173 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 132 = true ∨ valuation q 27 = true := by
  rw [value25, value27, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(194 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 132 = true ∨ valuation q 26 = true := by
  rw [value25, value26, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(193 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (194 : Vertex) [(193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 133 = true ∨ valuation q 29 = true := by
  rw [value26, value29, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 33 = false := by
  rw [value25, value27, value28, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (192 : Vertex) (198 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 135 = true ∨ valuation q 27 = true := by
  rw [value27, value28, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(194 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (206 : Vertex) [(194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 136 = true ∨ valuation q 31 = true ∨ valuation q 94 = true := by
  rw [value29, value31, value94, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (201 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(205 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (201 : Vertex) (193 : Vertex) [(205 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 40 = false := by
  rw [value29, value30, value31, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (201 : Vertex) (204 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 145 = true ∨ valuation q 37 = true := by
  rw [value37, value38, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (211 : Vertex) [(218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 145 = true ∨ valuation q 34 = true := by
  rw [value34, value38, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(211 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value41, value43, value47, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (265 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 148 = true ∨ valuation q 43 = true ∨ valuation q 47 = true := by
  rw [value41, value43, value47, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (321 : Vertex) [(261 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 149 = true ∨ valuation q 43 = true ∨ valuation q 44 = true := by
  rw [value42, value43, value44, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (276 : Vertex) [(261 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value41, value42, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value42, value44, value45, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 152 = true ∨ valuation q 43 = true ∨ valuation q 44 = true := by
  rw [value43, value44, value45, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (271 : Vertex) [(261 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 153 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value46, value48, value54, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(266 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (265 : Vertex) [(266 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 41 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value41, value46, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (264 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 41 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value41, value47, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (267 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value46, value47, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (264 : Vertex) (267 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value3, value51, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (278 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 53 = false ∨ valuation q 67 = false := by
  rw [value3, value51, value53, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (278 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 67 = false := by
  rw [value3, value51, value56, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (282 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 158 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 67 = true := by
  rw [value51, value53, value56, value67, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(278 : Vertex), (282 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (18 : Vertex) [(278 : Vertex), (282 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 58 = false := by
  rw [value42, value52, value53, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (278 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 159 = true ∨ valuation q 42 = true ∨ valuation q 58 = true := by
  rw [value42, value52, value58, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(260 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (278 : Vertex) [(260 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 160 = true ∨ valuation q 51 = true ∨ valuation q 52 = true := by
  rw [value51, value52, value53, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (262 : Vertex) [(274 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 160 = true ∨ valuation q 44 = true ∨ valuation q 51 = true := by
  rw [value44, value51, value53, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(262 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (276 : Vertex) [(262 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 46 = false ∨ valuation q 55 = false ∨ valuation q 58 = false := by
  rw [value46, value54, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (281 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E151.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112151
