import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 161 = true ∨ valuation q 18 = true ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 73 = true ∨ valuation q 111 = true := by
  rw [value18, value38, value39, value41, value42, value73, value111, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(62 : Vertex), (122 : Vertex), (124 : Vertex), (127 : Vertex), (254 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (118 : Vertex) [(62 : Vertex), (122 : Vertex), (124 : Vertex), (127 : Vertex), (254 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 161 = true ∨ valuation q 18 = true ∨ valuation q 34 = true ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 73 = true ∨ valuation q 111 = true := by
  rw [value18, value34, value39, value41, value42, value73, value111, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(62 : Vertex), (118 : Vertex), (124 : Vertex), (127 : Vertex), (254 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (122 : Vertex) [(62 : Vertex), (118 : Vertex), (124 : Vertex), (127 : Vertex), (254 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 19 = false ∨ valuation q 29 = false ∨ valuation q 40 = false := by
  rw [value19, value29, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (63 : Vertex) (111 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 19 = false ∨ valuation q 29 = false ∨ valuation q 41 = false := by
  rw [value19, value29, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (63 : Vertex) (111 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 19 = false ∨ valuation q 29 = false ∨ valuation q 74 = false := by
  rw [value19, value29, value42, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (63 : Vertex) (111 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 19 = false ∨ valuation q 35 = false ∨ valuation q 40 = false := by
  rw [value19, value35, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (63 : Vertex) (119 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 19 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value19, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (63 : Vertex) (125 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 29 = false ∨ valuation q 40 = false ∨ valuation q 74 = false := by
  rw [value29, value40, value42, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (111 : Vertex) (125 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 29 = false ∨ valuation q 41 = false ∨ valuation q 74 = false := by
  rw [value29, value41, value42, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (111 : Vertex) (126 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value35, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (119 : Vertex) (125 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 74 = false := by
  rw [value40, value41, value42, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (127 : Vertex) (125 : Vertex) (126 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 162 = true ∨ valuation q 29 = true ∨ valuation q 35 = true ∨ valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 74 = true := by
  rw [value29, value35, value40, value41, value42, value74, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (127 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(111 : Vertex), (119 : Vertex), (125 : Vertex), (126 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (127 : Vertex) (63 : Vertex) [(111 : Vertex), (119 : Vertex), (125 : Vertex), (126 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value43, value44, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 163 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value43, value47, value50, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(168 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(168 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 163 = true ∨ valuation q 44 = true ∨ valuation q 50 = true := by
  rw [value43, value44, value50, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (168 : Vertex) [(161 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 164 = true ∨ valuation q 45 = true := by
  rw [value44, value45, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 164 = true ∨ valuation q 43 = true := by
  rw [value43, value44, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(160 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (163 : Vertex) [(160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 52 = false := by
  rw [value44, value45, value46, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (167 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 165 = true ∨ valuation q 44 = true ∨ valuation q 52 = true := by
  rw [value44, value45, value52, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (163 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(161 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (163 : Vertex) (167 : Vertex) [(161 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 166 = true ∨ valuation q 49 = true := by
  rw [value46, value49, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(175 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (163 : Vertex) [(175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 166 = true ∨ valuation q 45 = true := by
  rw [value45, value46, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (175 : Vertex) [(163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 5 = false ∨ valuation q 43 = false ∨ valuation q 55 = false := by
  rw [value5, value43, value47, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (160 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 5 = false ∨ valuation q 43 = false ∨ valuation q 112 = false := by
  rw [value5, value43, value47, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (160 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 43 = false ∨ valuation q 55 = false ∨ valuation q 112 = false := by
  rw [value43, value47, value55, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (184 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 167 = true ∨ valuation q 5 = true ∨ valuation q 55 = true ∨ valuation q 112 = true := by
  rw [value5, value47, value55, value112, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(40 : Vertex), (184 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (160 : Vertex) [(40 : Vertex), (184 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 167 = true ∨ valuation q 5 = true ∨ valuation q 43 = true ∨ valuation q 112 = true := by
  rw [value5, value43, value47, value112, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(40 : Vertex), (160 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (184 : Vertex) [(40 : Vertex), (160 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 167 = true ∨ valuation q 5 = true ∨ valuation q 43 = true ∨ valuation q 55 = true := by
  rw [value5, value43, value47, value55, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(40 : Vertex), (160 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (424 : Vertex) [(40 : Vertex), (160 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 59 = true := by
  rw [value48, value59, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 49 = true := by
  rw [value48, value49, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 169 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(173 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (167 : Vertex) [(173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 169 = true ∨ valuation q 46 = true := by
  rw [value46, value49, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(167 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [(167 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 11 = false ∨ valuation q 43 = false ∨ valuation q 67 = false := by
  rw [value11, value43, value50, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (48 : Vertex) (160 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E040.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112040
