import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 72 = false := by
  rw [value17, value25, value37, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (57 : Vertex) (105 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 17 = false ∨ valuation q 40 = false ∨ valuation q 72 = false := by
  rw [value17, value37, value40, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (57 : Vertex) (125 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 17 = false ∨ valuation q 40 = false ∨ valuation q 107 = false := by
  rw [value17, value37, value40, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (57 : Vertex) (125 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 17 = false ∨ valuation q 72 = false ∨ valuation q 107 = false := by
  rw [value17, value37, value72, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (57 : Vertex) (249 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 25 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value25, value36, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (105 : Vertex) (120 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 25 = false ∨ valuation q 40 = false ∨ valuation q 72 = false := by
  rw [value25, value37, value40, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (105 : Vertex) (125 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 107 = false := by
  rw [value36, value37, value40, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (120 : Vertex) (125 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 157 = true ∨ valuation q 17 = true ∨ valuation q 25 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 107 = true := by
  rw [value17, value25, value36, value37, value40, value107, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(57 : Vertex), (105 : Vertex), (120 : Vertex), (125 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (249 : Vertex) [(57 : Vertex), (105 : Vertex), (120 : Vertex), (125 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 36 = true ∨ valuation q 41 = true ∨ valuation q 108 = true := by
  rw [value36, value38, value41, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(120 : Vertex), (126 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (114 : Vertex) [(120 : Vertex), (126 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 31 = true ∨ valuation q 41 = true ∨ valuation q 108 = true := by
  rw [value31, value38, value41, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(114 : Vertex), (126 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (120 : Vertex) [(114 : Vertex), (126 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 31 = true ∨ valuation q 36 = true ∨ valuation q 108 = true := by
  rw [value31, value36, value38, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(114 : Vertex), (120 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (126 : Vertex) [(114 : Vertex), (120 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 31 = true ∨ valuation q 36 = true ∨ valuation q 41 = true := by
  rw [value31, value36, value38, value41, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(114 : Vertex), (120 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (378 : Vertex) [(114 : Vertex), (120 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 27 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value27, value33, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (124 : Vertex) (108 : Vertex) (116 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 27 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value27, value36, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (124 : Vertex) (108 : Vertex) (120 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value33, value36, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (124 : Vertex) (116 : Vertex) (120 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 159 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value33, value36, value39, value40, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(116 : Vertex), (120 : Vertex), (125 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (108 : Vertex) [(116 : Vertex), (120 : Vertex), (125 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value27, value36, value39, value40, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(108 : Vertex), (120 : Vertex), (125 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (116 : Vertex) [(108 : Vertex), (120 : Vertex), (125 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 41 = true := by
  rw [value27, value33, value36, value39, value41, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(108 : Vertex), (116 : Vertex), (120 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(108 : Vertex), (116 : Vertex), (120 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 40 = true := by
  rw [value27, value33, value36, value39, value40, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(108 : Vertex), (116 : Vertex), (120 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(108 : Vertex), (116 : Vertex), (120 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 28 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value28, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (121 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 28 = false ∨ valuation q 37 = false ∨ valuation q 42 = false := by
  rw [value28, value37, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (121 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 28 = false ∨ valuation q 37 = false ∨ valuation q 110 = false := by
  rw [value28, value37, value40, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (121 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 28 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value28, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (124 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 28 = false ∨ valuation q 39 = false ∨ valuation q 110 = false := by
  rw [value28, value39, value40, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (124 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 28 = false ∨ valuation q 42 = false ∨ valuation q 110 = false := by
  rw [value28, value40, value42, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (109 : Vertex) (127 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value37, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (121 : Vertex) (124 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 110 = false := by
  rw [value37, value39, value40, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (121 : Vertex) (124 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 110 = false := by
  rw [value39, value40, value42, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (124 : Vertex) (127 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 160 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 110 = true := by
  rw [value37, value39, value40, value42, value110, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(121 : Vertex), (124 : Vertex), (127 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (109 : Vertex) [(121 : Vertex), (124 : Vertex), (127 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value18, value34, value38, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (62 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 39 = false := by
  rw [value18, value34, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (62 : Vertex) (118 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 42 = false := by
  rw [value18, value34, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (62 : Vertex) (118 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E040.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112040
