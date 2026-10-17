import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 167 = true ∨ valuation q 36 = true ∨ valuation q 40 = true ∨ valuation q 117 = true := by
  rw [value36, value39, value40, value117, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(233 : Vertex), (239 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (229 : Vertex) [(233 : Vertex), (239 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 167 = true ∨ valuation q 35 = true ∨ valuation q 40 = true ∨ valuation q 117 = true := by
  rw [value35, value39, value40, value117, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(229 : Vertex), (239 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (233 : Vertex) [(229 : Vertex), (239 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 167 = true ∨ valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 117 = true := by
  rw [value35, value36, value39, value117, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(229 : Vertex), (233 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (239 : Vertex) [(229 : Vertex), (233 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 49 = false := by
  rw [value38, value39, value40, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (235 : Vertex) (237 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 49 = true := by
  rw [value38, value40, value49, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(235 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (237 : Vertex) [(235 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value38, value39, value40, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(235 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (255 : Vertex) [(235 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value41, value42, value44, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (241 : Vertex) (244 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 169 = true ∨ valuation q 44 = true ∨ valuation q 46 = true := by
  rw [value41, value44, value46, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (241 : Vertex) → w ∈ [(244 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (241 : Vertex) [(244 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 169 = true ∨ valuation q 42 = true ∨ valuation q 44 = true := by
  rw [value41, value42, value44, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(241 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (248 : Vertex) [(241 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 170 = true ∨ valuation q 43 = true ∨ valuation q 119 = true := by
  rw [value42, value43, value119, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(243 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (240 : Vertex) [(243 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 170 = true ∨ valuation q 41 = true ∨ valuation q 119 = true := by
  rw [value41, value42, value119, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(240 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (243 : Vertex) [(240 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 170 = true ∨ valuation q 41 = true ∨ valuation q 43 = true := by
  rw [value41, value42, value43, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (241 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(240 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (241 : Vertex) (497 : Vertex) [(240 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 33 = true ∨ valuation q 42 = true ∨ valuation q 120 = true := by
  rw [value33, value42, value43, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ∈ [(227 : Vertex), (241 : Vertex), (499 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (243 : Vertex) [(227 : Vertex), (241 : Vertex), (499 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 33 = false ∨ valuation q 42 = false ∨ valuation q 120 = false := by
  rw [value33, value42, value43, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (243 : Vertex) (227 : Vertex) (241 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 33 = false ∨ valuation q 120 = false := by
  rw [value33, value120, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (243 : Vertex) (227 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 42 = false ∨ valuation q 120 = false := by
  rw [value42, value120, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (243 : Vertex) (241 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 171 = true ∨ valuation q 42 = true ∨ valuation q 120 = true := by
  rw [value42, value43, value120, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(241 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (227 : Vertex) [(241 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 171 = true ∨ valuation q 33 = true ∨ valuation q 120 = true := by
  rw [value33, value43, value120, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (241 : Vertex) → w ∈ [(227 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (241 : Vertex) [(227 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 171 = true ∨ valuation q 33 = true ∨ valuation q 42 = true := by
  rw [value33, value42, value43, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (243 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(227 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (243 : Vertex) (499 : Vertex) [(227 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value34, value41, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (228 : Vertex) (240 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 34 = false ∨ valuation q 41 = false ∨ valuation q 47 = false := by
  rw [value34, value41, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (228 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value41, value44, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (240 : Vertex) (246 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 172 = true ∨ valuation q 41 = true ∨ valuation q 45 = true ∨ valuation q 47 = true := by
  rw [value41, value44, value45, value47, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(240 : Vertex), (246 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (228 : Vertex) [(240 : Vertex), (246 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 172 = true ∨ valuation q 34 = true ∨ valuation q 41 = true ∨ valuation q 47 = true := by
  rw [value34, value41, value44, value47, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(228 : Vertex), (240 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (246 : Vertex) [(228 : Vertex), (240 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 44 = false ∨ valuation q 48 = false := by
  rw [value25, value44, value45, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (244 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 44 = false ∨ valuation q 122 = false := by
  rw [value25, value44, value45, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (244 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 25 = false ∨ valuation q 48 = false ∨ valuation q 122 = false := by
  rw [value25, value45, value48, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (182 : Vertex) (254 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 122 = false := by
  rw [value44, value45, value48, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (244 : Vertex) (254 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 27 = false ∨ valuation q 41 = false ∨ valuation q 47 = false := by
  rw [value27, value41, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (184 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 27 = false ∨ valuation q 41 = false ∨ valuation q 124 = false := by
  rw [value27, value41, value46, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (184 : Vertex) (240 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 27 = false ∨ valuation q 47 = false ∨ valuation q 124 = false := by
  rw [value27, value46, value47, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (184 : Vertex) (252 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 41 = false ∨ valuation q 47 = false ∨ valuation q 124 = false := by
  rw [value41, value46, value47, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (240 : Vertex) (252 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E034.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112034
