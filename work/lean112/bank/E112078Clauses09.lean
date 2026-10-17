import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 57 = false := by
  rw [value45, value46, value47, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (205 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 109 = false := by
  rw [value45, value46, value47, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (205 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 57 = false ∨ valuation q 109 = false := by
  rw [value45, value46, value57, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (205 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 57 = false ∨ valuation q 109 = false := by
  rw [value45, value47, value57, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (206 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 164 = true ∨ valuation q 8 = true ∨ valuation q 27 = true ∨ valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 57 = true := by
  rw [value8, value27, value45, value46, value47, value57, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(76 : Vertex), (140 : Vertex), (205 : Vertex), (206 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (460 : Vertex) [(76 : Vertex), (140 : Vertex), (205 : Vertex), (206 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value41, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (201 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 58 = false := by
  rw [value41, value43, value46, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (201 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value43, value45, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (201 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 48 = false ∨ valuation q 58 = false := by
  rw [value43, value46, value48, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (201 : Vertex) (207 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 165 = true ∨ valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 58 = true := by
  rw [value43, value45, value46, value48, value58, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(201 : Vertex), (204 : Vertex), (207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (197 : Vertex) [(201 : Vertex), (204 : Vertex), (207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 165 = true ∨ valuation q 41 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 58 = true := by
  rw [value41, value45, value46, value48, value58, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(197 : Vertex), (204 : Vertex), (207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (201 : Vertex) [(197 : Vertex), (204 : Vertex), (207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 165 = true ∨ valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 58 = true := by
  rw [value41, value43, value45, value46, value58, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(197 : Vertex), (201 : Vertex), (204 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (207 : Vertex) [(197 : Vertex), (201 : Vertex), (204 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 165 = true ∨ valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 48 = true := by
  rw [value41, value43, value45, value46, value48, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(197 : Vertex), (201 : Vertex), (204 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [(197 : Vertex), (201 : Vertex), (204 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 45 = false := by
  rw [value9, value28, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 59 = false := by
  rw [value9, value28, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 110 = false := by
  rw [value9, value28, value47, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (142 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value9, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 59 = false := by
  rw [value9, value45, value47, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (204 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 110 = false := by
  rw [value9, value45, value47, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 48 = false ∨ valuation q 110 = false := by
  rw [value9, value47, value48, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (207 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 110 = false := by
  rw [value44, value45, value47, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (202 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 45 = false ∨ valuation q 59 = false ∨ valuation q 110 = false := by
  rw [value45, value47, value59, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (204 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 42 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value42, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 167 = true ∨ valuation q 46 = true ∨ valuation q 47 = true := by
  rw [value46, value47, value48, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(205 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(205 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 167 = true ∨ valuation q 42 = true ∨ valuation q 47 = true := by
  rw [value42, value47, value48, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [(199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 37 = false := by
  rw [value10, value29, value37, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (144 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 50 = false := by
  rw [value10, value29, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (144 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 111 = false := by
  rw [value10, value29, value49, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (144 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 10 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value10, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 10 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value10, value49, value50, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 10 = false ∨ valuation q 50 = false ∨ valuation q 111 = false := by
  rw [value10, value49, value50, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (209 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 10 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value10, value49, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (80 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E078.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112078
