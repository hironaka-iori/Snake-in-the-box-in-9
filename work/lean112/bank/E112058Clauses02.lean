import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 29 = true := by
  rw [value29, value37, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (245 : Vertex) [(228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value37, value38, value39, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (244 : Vertex) (247 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 31 = false ∨ valuation q 38 = false ∨ valuation q 44 = false := by
  rw [value31, value38, value39, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (231 : Vertex) (245 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 38 = true ∨ valuation q 44 = true := by
  rw [value38, value39, value44, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(245 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (231 : Vertex) [(245 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 31 = true ∨ valuation q 44 = true := by
  rw [value31, value39, value44, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(231 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(231 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 33 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value33, value40, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (233 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 23 = false ∨ valuation q 34 = false ∨ valuation q 42 = false := by
  rw [value23, value34, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (186 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 113 = false := by
  rw [value34, value41, value42, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 41 = true ∨ valuation q 44 = true := by
  rw [value41, value42, value44, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(250 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (249 : Vertex) [(250 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 40 = true ∨ valuation q 44 = true := by
  rw [value40, value42, value44, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(249 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (250 : Vertex) [(249 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 25 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value25, value38, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (189 : Vertex) (245 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 115 = false := by
  rw [value38, value40, value43, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (245 : Vertex) (249 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value39, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 62 = false := by
  rw [value45, value46, value49, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (352 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 63 = true := by
  rw [value46, value50, value54, value63, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(297 : Vertex), (305 : Vertex), (353 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (288 : Vertex) [(297 : Vertex), (305 : Vertex), (353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 45 = true ∨ valuation q 54 = true ∨ valuation q 63 = true := by
  rw [value45, value46, value54, value63, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(288 : Vertex), (305 : Vertex), (353 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (297 : Vertex) [(288 : Vertex), (305 : Vertex), (353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value47, value48, value57, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (294 : Vertex) (295 : Vertex) (310 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 53 = true ∨ valuation q 68 = true := by
  rw [value48, value53, value68, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(303 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (294 : Vertex) [(303 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 47 = true ∨ valuation q 68 = true := by
  rw [value47, value48, value68, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(294 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (303 : Vertex) [(294 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 47 = true ∨ valuation q 53 = true := by
  rw [value47, value48, value53, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(294 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (359 : Vertex) [(294 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 50 = true ∨ valuation q 69 = true := by
  rw [value49, value50, value69, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(297 : Vertex), (360 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(297 : Vertex), (360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 69 = true := by
  rw [value45, value49, value69, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(288 : Vertex), (360 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (297 : Vertex) [(288 : Vertex), (360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 50 = true := by
  rw [value45, value49, value50, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(288 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (360 : Vertex) [(288 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value46, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (296 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value46, value49, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (296 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value46, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value49, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (296 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 71 = false := by
  rw [value50, value51, value53, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (299 : Vertex) (297 : Vertex) (303 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 53 = true ∨ valuation q 71 = true := by
  rw [value51, value53, value71, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(303 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (297 : Vertex) [(303 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 50 = true ∨ valuation q 71 = true := by
  rw [value50, value51, value71, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(297 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (303 : Vertex) [(297 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value50, value51, value53, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(297 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (363 : Vertex) [(297 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value50, value52, value53, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(297 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (317 : Vertex) [(297 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E058.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112058
