import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 155 = true ∨ valuation q 22 = true ∨ valuation q 37 = true ∨ valuation q 110 = true := by
  rw [value22, value37, value38, value110, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(145 : Vertex), (208 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (193 : Vertex) [(145 : Vertex), (208 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 155 = true ∨ valuation q 22 = true ∨ valuation q 29 = true ∨ valuation q 37 = true := by
  rw [value22, value29, value37, value38, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(145 : Vertex), (193 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (465 : Vertex) [(145 : Vertex), (193 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 30 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value30, value37, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 30 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value30, value39, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value41, value43, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 156 = true ∨ valuation q 30 = true ∨ valuation q 37 = true ∨ valuation q 43 = true := by
  rw [value30, value37, value39, value43, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (214 : Vertex) [(194 : Vertex), (208 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 156 = true ∨ valuation q 30 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value30, value37, value39, value41, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (218 : Vertex) [(194 : Vertex), (208 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value37, value40, value41, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (208 : Vertex) (214 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 157 = true ∨ valuation q 37 = true ∨ valuation q 44 = true := by
  rw [value37, value40, value44, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(208 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (214 : Vertex) [(208 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 157 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value37, value40, value41, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(208 : Vertex), (214 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (220 : Vertex) [(208 : Vertex), (214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 158 = true ∨ valuation q 40 = true ∨ valuation q 45 = true := by
  rw [value40, value41, value45, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(212 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (210 : Vertex) [(212 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 158 = true ∨ valuation q 39 = true ∨ valuation q 45 = true := by
  rw [value39, value41, value45, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(210 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (212 : Vertex) [(210 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 158 = true ∨ valuation q 39 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value41, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(210 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(210 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 13 = false ∨ valuation q 37 = false ∨ valuation q 43 = false := by
  rw [value13, value37, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 13 = false ∨ valuation q 37 = false ∨ valuation q 44 = false := by
  rw [value13, value37, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 13 = false ∨ valuation q 37 = false ∨ valuation q 114 = false := by
  rw [value13, value37, value42, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (208 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 13 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value13, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 13 = false ∨ valuation q 43 = false ∨ valuation q 114 = false := by
  rw [value13, value42, value43, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 13 = false ∨ valuation q 44 = false ∨ valuation q 114 = false := by
  rw [value13, value42, value44, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value37, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 114 = false := by
  rw [value37, value42, value43, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 44 = false ∨ valuation q 114 = false := by
  rw [value37, value42, value44, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (208 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 114 = false := by
  rw [value42, value43, value44, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (218 : Vertex) (220 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 159 = true ∨ valuation q 13 = true ∨ valuation q 37 = true ∨ valuation q 43 = true ∨ valuation q 114 = true := by
  rw [value13, value37, value42, value43, value114, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(88 : Vertex), (208 : Vertex), (218 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (220 : Vertex) [(88 : Vertex), (208 : Vertex), (218 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 159 = true ∨ valuation q 13 = true ∨ valuation q 37 = true ∨ valuation q 43 = true ∨ valuation q 44 = true := by
  rw [value13, value37, value42, value43, value44, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(88 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (472 : Vertex) [(88 : Vertex), (208 : Vertex), (218 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 160 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value42, value43, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (210 : Vertex) [(216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 160 = true ∨ valuation q 39 = true ∨ valuation q 45 = true := by
  rw [value39, value43, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(210 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (216 : Vertex) [(210 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 160 = true ∨ valuation q 39 = true ∨ valuation q 42 = true := by
  rw [value39, value42, value43, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(210 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (222 : Vertex) [(210 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 40 = false ∨ valuation q 42 = false := by
  rw [value34, value40, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (212 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value34, value42, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (220 : Vertex) (204 : Vertex) (216 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true ∨ valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value40, value42, value44, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(212 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(212 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true ∨ valuation q 34 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value34, value42, value44, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(204 : Vertex), (216 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (212 : Vertex) [(204 : Vertex), (216 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E064.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112064
