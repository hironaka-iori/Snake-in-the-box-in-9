import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 29 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value29, value34, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (139 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 29 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value29, value34, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (129 : Vertex) (141 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value34, value36, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (139 : Vertex) (141 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 46 = true := by
  rw [value34, value36, value37, value46, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(139 : Vertex), (141 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (129 : Vertex) [(139 : Vertex), (141 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 29 = true ∨ valuation q 37 = true ∨ valuation q 46 = true := by
  rw [value29, value34, value37, value46, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (139 : Vertex) [(129 : Vertex), (141 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 29 = true ∨ valuation q 36 = true ∨ valuation q 46 = true := by
  rw [value29, value34, value36, value46, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(129 : Vertex), (139 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (141 : Vertex) [(129 : Vertex), (139 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 29 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value29, value34, value36, value37, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(129 : Vertex), (139 : Vertex), (141 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (153 : Vertex) [(129 : Vertex), (139 : Vertex), (141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 90 = false := by
  rw [value35, value36, value38, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (142 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 47 = false ∨ valuation q 56 = false := by
  rw [value35, value36, value47, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (154 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 47 = false ∨ valuation q 90 = false := by
  rw [value35, value36, value47, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (154 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 56 = false ∨ valuation q 90 = false := by
  rw [value35, value36, value56, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (202 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 47 = false ∨ valuation q 56 = false := by
  rw [value35, value38, value47, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (142 : Vertex) (154 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 47 = false ∨ valuation q 90 = false := by
  rw [value35, value38, value47, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (142 : Vertex) (154 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 36 = true ∨ valuation q 38 = true ∨ valuation q 47 = true ∨ valuation q 56 = true := by
  rw [value35, value36, value38, value47, value56, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(139 : Vertex), (142 : Vertex), (154 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (394 : Vertex) [(139 : Vertex), (142 : Vertex), (154 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value30, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 39 = false := by
  rw [value30, value34, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 30 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value30, value35, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value34, value35, value36, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (137 : Vertex) (138 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value3, value32, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 32 = false ∨ valuation q 39 = false := by
  rw [value3, value32, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 32 = false ∨ valuation q 48 = false := by
  rw [value3, value32, value37, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 32 = false ∨ valuation q 58 = false := by
  rw [value3, value32, value37, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 32 = false ∨ valuation q 92 = false := by
  rw [value3, value32, value37, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (133 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 34 = false ∨ valuation q 39 = false := by
  rw [value3, value34, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (137 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 34 = false ∨ valuation q 48 = false := by
  rw [value3, value34, value37, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (137 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 34 = false ∨ valuation q 58 = false := by
  rw [value3, value34, value37, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (137 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 34 = false ∨ valuation q 92 = false := by
  rw [value3, value34, value37, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (137 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 39 = false ∨ valuation q 48 = false := by
  rw [value3, value37, value39, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (143 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 39 = false ∨ valuation q 58 = false := by
  rw [value3, value37, value39, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (143 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 39 = false ∨ valuation q 92 = false := by
  rw [value3, value37, value39, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (143 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 58 = false := by
  rw [value3, value37, value48, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (157 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 92 = false := by
  rw [value3, value37, value48, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (13 : Vertex) (157 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E158.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112158
