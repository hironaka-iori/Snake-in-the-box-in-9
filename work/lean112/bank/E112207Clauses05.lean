import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 153 = true := by
  rw [value36, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = true ∨ valuation q 41 = true := by
  rw [value33, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ∈ [(198 : Vertex), (222 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (214 : Vertex) [(198 : Vertex), (222 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 154 = true ∨ valuation q 41 = true := by
  rw [value37, value41, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 154 = true ∨ valuation q 33 = true := by
  rw [value33, value37, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(198 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 38 = true := by
  rw [value38, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (218 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 155 = true ∨ valuation q 41 = true := by
  rw [value38, value41, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 155 = true ∨ valuation q 29 = true := by
  rw [value29, value38, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(154 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (222 : Vertex) [(154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ∈ [(221 : Vertex), (222 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (220 : Vertex) [(221 : Vertex), (222 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 156 = true ∨ valuation q 41 = true := by
  rw [value39, value41, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (221 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 156 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value31, value35, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (157 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 157 = true ∨ valuation q 31 = true ∨ valuation q 39 = true := by
  rw [value31, value39, value40, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(157 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (205 : Vertex) [(157 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 157 = true ∨ valuation q 31 = true ∨ valuation q 35 = true := by
  rw [value31, value35, value40, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(157 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (220 : Vertex) [(157 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value37, value38, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 158 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value38, value39, value41, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(218 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (214 : Vertex) [(218 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 158 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value37, value38, value41, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(214 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (220 : Vertex) [(214 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 159 = true := by
  rw [value42, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (226 : Vertex) (230 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 42 = true ∨ valuation q 44 = true := by
  rw [value33, value42, value43, value44, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(198 : Vertex), (226 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (486 : Vertex) [(198 : Vertex), (226 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true := by
  rw [value44, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (238 : Vertex) (230 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value1, value45, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (257 : Vertex) (260 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 46 = false ∨ valuation q 52 = false := by
  rw [value1, value45, value46, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (257 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 46 = false ∨ valuation q 68 = false := by
  rw [value1, value45, value46, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (257 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 46 = false ∨ valuation q 85 = false := by
  rw [value1, value45, value46, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (257 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value1, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (258 : Vertex) (260 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 47 = false ∨ valuation q 52 = false := by
  rw [value1, value45, value47, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (258 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 47 = false ∨ valuation q 68 = false := by
  rw [value1, value45, value47, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (258 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 47 = false ∨ valuation q 85 = false := by
  rw [value1, value45, value47, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (258 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value1, value45, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (260 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 48 = false ∨ valuation q 68 = false := by
  rw [value1, value45, value48, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (260 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 48 = false ∨ valuation q 85 = false := by
  rw [value1, value45, value48, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (260 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value1, value45, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (264 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value1, value45, value52, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (264 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E207.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112207
