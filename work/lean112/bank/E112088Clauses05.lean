import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 29 = true := by
  rw [value20, value29, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(173 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(173 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value20, value28, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(173 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (188 : Vertex) [(173 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 31 = true := by
  rw [value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (190 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value21, value27, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (174 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value21, value27, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (190 : Vertex) (174 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 21 = false ∨ valuation q 29 = false := by
  rw [value21, value29, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (190 : Vertex) (174 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value27, value29, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(182 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (174 : Vertex) [(182 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 21 = true ∨ valuation q 29 = true := by
  rw [value21, value29, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(174 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (182 : Vertex) [(174 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 21 = true ∨ valuation q 27 = true := by
  rw [value21, value27, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(174 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (188 : Vertex) [(174 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 34 = false ∨ valuation q 38 = false := by
  rw [value12, value32, value34, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (160 : Vertex) (228 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 34 = true ∨ valuation q 38 = true ∨ valuation q 99 = true := by
  rw [value32, value34, value38, value99, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(228 : Vertex), (232 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (160 : Vertex) [(228 : Vertex), (232 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 12 = true ∨ valuation q 38 = true ∨ valuation q 99 = true := by
  rw [value12, value32, value38, value99, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(160 : Vertex), (232 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (228 : Vertex) [(160 : Vertex), (232 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 12 = true ∨ valuation q 34 = true ∨ valuation q 38 = true := by
  rw [value12, value32, value34, value38, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(160 : Vertex), (228 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (480 : Vertex) [(160 : Vertex), (228 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 37 = false := by
  rw [value1, value14, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (163 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value1, value14, value33, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (163 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value1, value33, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (231 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 37 = false ∨ valuation q 44 = false := by
  rw [value1, value33, value37, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (231 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 37 = false ∨ valuation q 101 = false := by
  rw [value1, value33, value37, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (231 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value1, value33, value41, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (235 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 41 = false ∨ valuation q 101 = false := by
  rw [value1, value33, value41, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (235 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 1 = false ∨ valuation q 44 = false ∨ valuation q 101 = false := by
  rw [value1, value33, value44, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (243 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 14 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value14, value33, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (163 : Vertex) (231 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value33, value37, value41, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (231 : Vertex) (235 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 101 = false := by
  rw [value33, value41, value44, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (235 : Vertex) (243 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value32, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (229 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value32, value34, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (229 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 45 = false := by
  rw [value32, value34, value35, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (229 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 42 = false := by
  rw [value32, value34, value36, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 45 = false := by
  rw [value32, value34, value36, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value32, value34, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 42 = false := by
  rw [value34, value35, value36, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 45 = false := by
  rw [value34, value35, value36, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E088.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112088
