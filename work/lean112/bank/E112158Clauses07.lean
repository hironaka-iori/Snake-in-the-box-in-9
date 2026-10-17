import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 4 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 60 = true := by
  rw [value4, value33, value36, value37, value39, value60, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(15 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (142 : Vertex) [(15 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 4 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value4, value33, value36, value37, value38, value39, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (143 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(15 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (143 : Vertex) (207 : Vertex) [(15 : Vertex), (135 : Vertex), (139 : Vertex), (141 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value40, value41, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 61 = false := by
  rw [value40, value41, value42, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 93 = false := by
  rw [value40, value41, value42, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 61 = false := by
  rw [value40, value41, value45, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (152 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 93 = false := by
  rw [value40, value41, value45, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 61 = false ∨ valuation q 93 = false := by
  rw [value40, value41, value61, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (208 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 61 = false := by
  rw [value40, value42, value45, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 93 = false := by
  rw [value40, value42, value45, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 61 = false ∨ valuation q 93 = false := by
  rw [value40, value42, value61, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (208 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 45 = false ∨ valuation q 61 = false ∨ valuation q 93 = false := by
  rw [value40, value45, value61, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (152 : Vertex) (208 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 43 = true ∨ valuation q 47 = true := by
  rw [value41, value43, value47, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(150 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(150 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 40 = true ∨ valuation q 47 = true := by
  rw [value40, value41, value47, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(144 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (150 : Vertex) [(144 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 40 = true ∨ valuation q 43 = true := by
  rw [value40, value41, value43, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(144 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (154 : Vertex) [(144 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 43 = true ∨ valuation q 64 = true := by
  rw [value31, value42, value43, value64, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(132 : Vertex), (150 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(132 : Vertex), (150 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 31 = true ∨ valuation q 40 = true ∨ valuation q 64 = true := by
  rw [value31, value40, value42, value64, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (150 : Vertex) [(132 : Vertex), (144 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 44 = false := by
  rw [value41, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (146 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 161 = true ∨ valuation q 42 = true ∨ valuation q 44 = true := by
  rw [value42, value43, value44, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(148 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (146 : Vertex) [(148 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 43 = true ∨ valuation q 66 = true ∨ valuation q 96 = true := by
  rw [value43, value44, value66, value96, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(150 : Vertex), (215 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (135 : Vertex) [(150 : Vertex), (215 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 33 = true ∨ valuation q 43 = true ∨ valuation q 96 = true := by
  rw [value33, value43, value44, value96, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(135 : Vertex), (150 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (215 : Vertex) [(135 : Vertex), (150 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 33 = true ∨ valuation q 43 = true ∨ valuation q 66 = true := by
  rw [value33, value43, value44, value66, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(135 : Vertex), (150 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (407 : Vertex) [(135 : Vertex), (150 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value40, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (144 : Vertex) (153 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 163 = true ∨ valuation q 46 = true ∨ valuation q 47 = true := by
  rw [value45, value46, value47, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (144 : Vertex) [(153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 163 = true ∨ valuation q 40 = true ∨ valuation q 47 = true := by
  rw [value40, value45, value47, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(144 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (153 : Vertex) [(144 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 163 = true ∨ valuation q 40 = true ∨ valuation q 46 = true := by
  rw [value40, value45, value46, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(144 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (154 : Vertex) [(144 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 34 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value34, value45, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (153 : Vertex) (137 : Vertex) (152 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 45 = true ∨ valuation q 48 = true := by
  rw [value45, value46, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(152 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (137 : Vertex) [(152 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 34 = true ∨ valuation q 48 = true := by
  rw [value34, value46, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(137 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (152 : Vertex) [(137 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 34 = true ∨ valuation q 45 = true := by
  rw [value34, value45, value46, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (153 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(137 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (153 : Vertex) (157 : Vertex) [(137 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value35, value41, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (146 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 35 = false ∨ valuation q 41 = false := by
  rw [value35, value41, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (154 : Vertex) (138 : Vertex) (146 : Vertex) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E158.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112158
