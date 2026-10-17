import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value38, value43, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (244 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 38 = false ∨ valuation q 110 = false := by
  rw [value38, value110, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (244 : Vertex) (240 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 43 = false ∨ valuation q 110 = false := by
  rw [value43, value110, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (244 : Vertex) (252 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 41 = true := by
  rw [value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 159 = true := by
  rw [value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 45 = false := by
  rw [value35, value40, value42, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (242 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 35 = false ∨ valuation q 45 = false := by
  rw [value35, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (250 : Vertex) (234 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 35 = true ∨ valuation q 45 = true := by
  rw [value35, value42, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (250 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(234 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (250 : Vertex) (242 : Vertex) [(234 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 35 = true ∨ valuation q 40 = true := by
  rw [value35, value40, value42, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (250 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(234 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (250 : Vertex) (254 : Vertex) [(234 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value36, value41, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (252 : Vertex) (236 : Vertex) (244 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value36, value41, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (252 : Vertex) (236 : Vertex) (244 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 41 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value41, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (252 : Vertex) (244 : Vertex) (253 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 36 = false ∨ valuation q 41 = false := by
  rw [value36, value41, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (252 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 117 = false := by
  rw [value37, value44, value46, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (237 : Vertex) (255 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 117 = true := by
  rw [value43, value44, value46, value117, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(252 : Vertex), (255 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (237 : Vertex) [(252 : Vertex), (255 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 162 = true ∨ valuation q 37 = true ∨ valuation q 43 = true ∨ valuation q 117 = true := by
  rw [value37, value43, value44, value117, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(237 : Vertex), (252 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (255 : Vertex) [(237 : Vertex), (252 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 163 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value45, value46, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(252 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (250 : Vertex) [(252 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 163 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value45, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(250 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (255 : Vertex) [(250 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 118 = false := by
  rw [value44, value45, value46, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (253 : Vertex) (254 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 44 = true ∨ valuation q 118 = true := by
  rw [value44, value46, value118, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(253 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (254 : Vertex) [(253 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value47, value48, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 167 = true ∨ valuation q 47 = true := by
  rw [value47, value49, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(257 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (269 : Vertex) [(257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true := by
  rw [value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (268 : Vertex) (269 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 47 = true := by
  rw [value47, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(257 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (272 : Vertex) [(257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value62, value63, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (355 : Vertex) (357 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 98 = true := by
  rw [value63, value66, value68, value98, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(359 : Vertex), (363 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (353 : Vertex) [(359 : Vertex), (363 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 98 = true := by
  rw [value62, value63, value68, value98, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(353 : Vertex), (363 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (359 : Vertex) [(353 : Vertex), (363 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 62 = true ∨ valuation q 66 = true ∨ valuation q 98 = true := by
  rw [value62, value63, value66, value98, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(353 : Vertex), (359 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (363 : Vertex) [(353 : Vertex), (359 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 62 = true ∨ valuation q 66 = true ∨ valuation q 68 = true := by
  rw [value62, value63, value66, value68, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(353 : Vertex), (359 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (483 : Vertex) [(353 : Vertex), (359 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 14 = false ∨ valuation q 69 = false ∨ valuation q 99 = false := by
  rw [value14, value64, value69, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (100 : Vertex) (364 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 99 = false := by
  rw [value64, value65, value69, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (357 : Vertex) (364 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 182 = true ∨ valuation q 14 = true ∨ valuation q 65 = true ∨ valuation q 99 = true := by
  rw [value14, value64, value65, value99, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (364 : Vertex) → w ∈ [(100 : Vertex), (357 : Vertex), (484 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (364 : Vertex) [(100 : Vertex), (357 : Vertex), (484 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E104.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112104
