import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value33, value35, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 44 = false := by
  rw [value33, value35, value38, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (137 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 44 = false := by
  rw [value33, value37, value38, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (140 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 44 = false := by
  rw [value35, value37, value38, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (137 : Vertex) (140 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 44 = true := by
  rw [value33, value37, value38, value44, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(133 : Vertex), (140 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (137 : Vertex) [(133 : Vertex), (140 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 37 = true := by
  rw [value33, value35, value37, value38, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(133 : Vertex), (137 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (157 : Vertex) [(133 : Vertex), (137 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 41 = true := by
  rw [value39, value41, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(146 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (145 : Vertex) [(146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(145 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (146 : Vertex) [(145 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 164 = true ∨ valuation q 39 = true ∨ valuation q 58 = true := by
  rw [value39, value40, value58, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(144 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (129 : Vertex) [(144 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 164 = true ∨ valuation q 30 = true ∨ valuation q 58 = true := by
  rw [value30, value40, value58, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(129 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (144 : Vertex) [(129 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 164 = true ∨ valuation q 30 = true ∨ valuation q 39 = true := by
  rw [value30, value39, value40, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(129 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (209 : Vertex) [(129 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 41 = true := by
  rw [value41, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (146 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value39, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (144 : Vertex) (150 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value41, value42, value43, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(150 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(150 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 39 = true ∨ valuation q 43 = true := by
  rw [value39, value41, value43, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(144 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (150 : Vertex) [(144 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 39 = true ∨ valuation q 42 = true := by
  rw [value39, value41, value42, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(144 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (154 : Vertex) [(144 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 61 = false := by
  rw [value41, value42, value45, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (146 : Vertex) (158 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 45 = true ∨ valuation q 61 = true := by
  rw [value42, value45, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (146 : Vertex) → w ∈ [(158 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (146 : Vertex) [(158 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 41 = true ∨ valuation q 61 = true := by
  rw [value41, value42, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(146 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (158 : Vertex) [(146 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 99 = false := by
  rw [value41, value43, value45, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (146 : Vertex) (158 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 44 = true := by
  rw [value44, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (157 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 38 = true ∨ valuation q 46 = true := by
  rw [value38, value44, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ∈ [(141 : Vertex), (159 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (157 : Vertex) [(141 : Vertex), (159 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 46 = true := by
  rw [value44, value46, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(159 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (141 : Vertex) [(159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 168 = true ∨ valuation q 38 = true := by
  rw [value38, value44, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(141 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (159 : Vertex) [(141 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value42, value43, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (158 : Vertex) (150 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value45, value46, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (150 : Vertex) [(154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 46 = true := by
  rw [value42, value45, value46, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(150 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (154 : Vertex) [(150 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value45, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(150 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(150 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 45 = true := by
  rw [value45, value46, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (157 : Vertex) [(158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 170 = true ∨ valuation q 44 = true := by
  rw [value44, value46, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(157 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value47, value48, value49, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 102 = false := by
  rw [value47, value48, value49, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E105.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112105
