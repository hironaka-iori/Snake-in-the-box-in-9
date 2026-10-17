import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 157 = true ∨ valuation q 36 = true ∨ valuation q 38 = true := by
  rw [value36, value38, value41, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(230 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (236 : Vertex) [(230 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 10 = false ∨ valuation q 22 = false ∨ valuation q 44 = false := by
  rw [value10, value22, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (177 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 10 = false ∨ valuation q 32 = false ∨ valuation q 44 = false := by
  rw [value10, value32, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (225 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 10 = false ∨ valuation q 44 = false ∨ valuation q 47 = false := by
  rw [value10, value42, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (245 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 10 = false ∨ valuation q 44 = false ∨ valuation q 108 = false := by
  rw [value10, value42, value44, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (245 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 10 = false ∨ valuation q 47 = false ∨ valuation q 108 = false := by
  rw [value10, value42, value47, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (241 : Vertex) (113 : Vertex) (249 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 34 = true ∨ valuation q 44 = true ∨ valuation q 111 = true := by
  rw [value34, value43, value44, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ∈ [(228 : Vertex), (245 : Vertex), (500 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (244 : Vertex) [(228 : Vertex), (245 : Vertex), (500 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 34 = false ∨ valuation q 44 = false ∨ valuation q 111 = false := by
  rw [value34, value43, value44, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (228 : Vertex) (245 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 44 = true ∨ valuation q 111 = true := by
  rw [value43, value44, value111, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(245 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (228 : Vertex) [(245 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 34 = true ∨ valuation q 111 = true := by
  rw [value34, value43, value111, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (245 : Vertex) [(228 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 34 = true ∨ valuation q 44 = true := by
  rw [value34, value43, value44, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(228 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (500 : Vertex) [(228 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value35, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (241 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value35, value42, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (241 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 35 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value35, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (244 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value42, value43, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (241 : Vertex) (244 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 42 = true ∨ valuation q 43 = true ∨ valuation q 45 = true := by
  rw [value42, value43, value44, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(241 : Vertex), (244 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [(241 : Vertex), (244 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 45 = true := by
  rw [value35, value42, value44, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(229 : Vertex), (241 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (244 : Vertex) [(229 : Vertex), (241 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 43 = true := by
  rw [value35, value42, value43, value44, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(229 : Vertex), (241 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (247 : Vertex) [(229 : Vertex), (241 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 45 = true := by
  rw [value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (247 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = true ∨ valuation q 50 = true := by
  rw [value44, value45, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ∈ [(245 : Vertex), (255 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (247 : Vertex) [(245 : Vertex), (255 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 44 = false ∨ valuation q 50 = false := by
  rw [value44, value50, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (247 : Vertex) (245 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 161 = true ∨ valuation q 50 = true := by
  rw [value45, value50, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 161 = true ∨ valuation q 44 = true := by
  rw [value44, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 46 = true := by
  rw [value46, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (248 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 26 = true ∨ valuation q 37 = true ∨ valuation q 47 = true ∨ valuation q 48 = true := by
  rw [value26, value37, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ∈ [(184 : Vertex), (232 : Vertex), (249 : Vertex), (250 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (248 : Vertex) [(184 : Vertex), (232 : Vertex), (249 : Vertex), (250 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 26 = false ∨ valuation q 37 = false ∨ valuation q 47 = false := by
  rw [value26, value37, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (184 : Vertex) (232 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 26 = false ∨ valuation q 37 = false ∨ valuation q 48 = false := by
  rw [value26, value37, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (184 : Vertex) (232 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 26 = false ∨ valuation q 48 = false := by
  rw [value26, value48, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (248 : Vertex) (184 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 37 = true ∨ valuation q 47 = true ∨ valuation q 48 = true := by
  rw [value37, value46, value47, value48, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(232 : Vertex), (249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(232 : Vertex), (249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 26 = true ∨ valuation q 47 = true ∨ valuation q 48 = true := by
  rw [value26, value46, value47, value48, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(184 : Vertex), (249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (232 : Vertex) [(184 : Vertex), (249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 26 = true ∨ valuation q 37 = true ∨ valuation q 48 = true := by
  rw [value26, value37, value46, value48, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(184 : Vertex), (232 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(184 : Vertex), (232 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 26 = true ∨ valuation q 37 = true ∨ valuation q 47 = true := by
  rw [value26, value37, value46, value47, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(184 : Vertex), (232 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (250 : Vertex) [(184 : Vertex), (232 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E169.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112169
