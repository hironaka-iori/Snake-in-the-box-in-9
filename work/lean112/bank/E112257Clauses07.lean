import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 38 = true ∨ valuation q 43 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value38, value43, value44, value55, value65, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(133 : Vertex), (140 : Vertex), (157 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (13 : Vertex) [(133 : Vertex), (140 : Vertex), (157 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 8 = true ∨ valuation q 43 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value8, value43, value44, value55, value65, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(13 : Vertex), (140 : Vertex), (157 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (133 : Vertex) [(13 : Vertex), (140 : Vertex), (157 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 8 = true ∨ valuation q 38 = true ∨ valuation q 43 = true ∨ valuation q 55 = true := by
  rw [value8, value38, value43, value44, value55, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(13 : Vertex), (133 : Vertex), (140 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (173 : Vertex) [(13 : Vertex), (133 : Vertex), (140 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 9 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value9, value39, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (14 : Vertex) (134 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 9 = false ∨ valuation q 43 = false ∨ valuation q 56 = false := by
  rw [value9, value43, value45, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (14 : Vertex) (140 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 56 = false := by
  rw [value39, value41, value45, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (138 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 56 = false := by
  rw [value39, value43, value45, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (140 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 56 = false := by
  rw [value41, value43, value45, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (138 : Vertex) (140 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 10 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value10, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (16 : Vertex) (145 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 10 = false ∨ valuation q 47 = false ∨ valuation q 67 = false := by
  rw [value10, value46, value47, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (16 : Vertex) (145 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 36 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value36, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (145 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 36 = false ∨ valuation q 47 = false ∨ valuation q 67 = false := by
  rw [value36, value46, value47, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (145 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 36 = false ∨ valuation q 51 = false ∨ valuation q 67 = false := by
  rw [value36, value46, value51, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (152 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 67 = false := by
  rw [value46, value47, value51, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (145 : Vertex) (152 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 36 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 67 = true := by
  rw [value36, value46, value47, value51, value67, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(128 : Vertex), (145 : Vertex), (152 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (16 : Vertex) [(128 : Vertex), (145 : Vertex), (152 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 10 = true ∨ valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 67 = true := by
  rw [value10, value46, value47, value51, value67, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(16 : Vertex), (145 : Vertex), (152 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (128 : Vertex) [(16 : Vertex), (145 : Vertex), (152 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 10 = true ∨ valuation q 36 = true ∨ valuation q 47 = true ∨ valuation q 51 = true := by
  rw [value10, value36, value46, value47, value51, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(16 : Vertex), (128 : Vertex), (145 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (176 : Vertex) [(16 : Vertex), (128 : Vertex), (145 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 11 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value11, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (17 : Vertex) (144 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 11 = false ∨ valuation q 46 = false ∨ valuation q 52 = false := by
  rw [value11, value46, value47, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (17 : Vertex) (144 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 11 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value11, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (17 : Vertex) (147 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 11 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value11, value47, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (17 : Vertex) (147 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 11 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value11, value47, value49, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (17 : Vertex) (149 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value46, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (144 : Vertex) (147 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value46, value47, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (144 : Vertex) (147 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value46, value47, value49, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (144 : Vertex) (149 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value47, value48, value49, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (147 : Vertex) (149 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 52 = true := by
  rw [value46, value47, value48, value49, value52, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(144 : Vertex), (147 : Vertex), (149 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (17 : Vertex) [(144 : Vertex), (147 : Vertex), (149 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 11 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value11, value46, value47, value48, value52, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(17 : Vertex), (144 : Vertex), (147 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (149 : Vertex) [(17 : Vertex), (144 : Vertex), (147 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 53 = false := by
  rw [value37, value47, value48, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (145 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 37 = false ∨ valuation q 53 = false ∨ valuation q 69 = false := by
  rw [value37, value48, value53, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (155 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 69 = true := by
  rw [value47, value48, value53, value69, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(145 : Vertex), (155 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (131 : Vertex) [(145 : Vertex), (155 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 37 = true ∨ valuation q 53 = true ∨ valuation q 69 = true := by
  rw [value37, value48, value53, value69, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(131 : Vertex), (155 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (145 : Vertex) [(131 : Vertex), (155 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E257.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112257
