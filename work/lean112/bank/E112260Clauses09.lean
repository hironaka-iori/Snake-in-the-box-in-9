import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 5 = true ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value5, value41, value46, value51, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(71 : Vertex), (207 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (197 : Vertex) [(71 : Vertex), (207 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 5 = true ∨ valuation q 40 = true ∨ valuation q 51 = true := by
  rw [value5, value40, value41, value51, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(71 : Vertex), (197 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(71 : Vertex), (197 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 168 = true ∨ valuation q 5 = true ∨ valuation q 40 = true ∨ valuation q 46 = true := by
  rw [value5, value40, value41, value46, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(71 : Vertex), (197 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (215 : Vertex) [(71 : Vertex), (197 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 42 = true := by
  rw [value42, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (202 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = true ∨ valuation q 43 = true ∨ valuation q 53 = true := by
  rw [value38, value42, value43, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ∈ [(194 : Vertex), (203 : Vertex), (218 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (202 : Vertex) [(194 : Vertex), (203 : Vertex), (218 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 53 = false := by
  rw [value38, value42, value43, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (203 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 38 = false ∨ valuation q 53 = false := by
  rw [value38, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (202 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 43 = false ∨ valuation q 53 = false := by
  rw [value43, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (202 : Vertex) (203 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 43 = true ∨ valuation q 53 = true := by
  rw [value42, value43, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(203 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (194 : Vertex) [(203 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 38 = true ∨ valuation q 53 = true := by
  rw [value38, value42, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(194 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (203 : Vertex) [(194 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 169 = true ∨ valuation q 38 = true ∨ valuation q 43 = true := by
  rw [value38, value42, value43, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(194 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (218 : Vertex) [(194 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 46 = false := by
  rw [value7, value42, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (202 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 62 = false := by
  rw [value7, value42, value43, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (202 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 110 = false := by
  rw [value7, value42, value43, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (202 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 7 = false ∨ valuation q 46 = false ∨ valuation q 62 = false := by
  rw [value7, value43, value46, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (207 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 7 = false ∨ valuation q 46 = false ∨ valuation q 110 = false := by
  rw [value7, value43, value46, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (207 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 46 = false ∨ valuation q 62 = false := by
  rw [value42, value43, value46, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (202 : Vertex) (207 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 46 = false ∨ valuation q 110 = false := by
  rw [value42, value43, value46, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (202 : Vertex) (207 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 170 = true ∨ valuation q 42 = true ∨ valuation q 46 = true ∨ valuation q 62 = true ∨ valuation q 110 = true := by
  rw [value42, value43, value46, value62, value110, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(202 : Vertex), (207 : Vertex), (235 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (75 : Vertex) [(202 : Vertex), (207 : Vertex), (235 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 170 = true ∨ valuation q 7 = true ∨ valuation q 42 = true ∨ valuation q 62 = true ∨ valuation q 110 = true := by
  rw [value7, value42, value43, value62, value110, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(75 : Vertex), (202 : Vertex), (235 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (207 : Vertex) [(75 : Vertex), (202 : Vertex), (235 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 170 = true ∨ valuation q 7 = true ∨ valuation q 42 = true ∨ valuation q 46 = true ∨ valuation q 62 = true := by
  rw [value7, value42, value43, value46, value62, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(75 : Vertex), (202 : Vertex), (207 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (459 : Vertex) [(75 : Vertex), (202 : Vertex), (207 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 39 = false ∨ valuation q 45 = false := by
  rw [value8, value39, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 39 = false ∨ valuation q 54 = false := by
  rw [value8, value39, value44, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 39 = false ∨ valuation q 63 = false := by
  rw [value8, value39, value44, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 45 = false ∨ valuation q 54 = false := by
  rw [value8, value44, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 45 = false ∨ valuation q 63 = false := by
  rw [value8, value44, value45, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (205 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 54 = false ∨ valuation q 63 = false := by
  rw [value8, value44, value54, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (220 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 39 = false ∨ valuation q 45 = false ∨ valuation q 54 = false := by
  rw [value39, value44, value45, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (205 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 39 = true ∨ valuation q 45 = true ∨ valuation q 54 = true ∨ valuation q 63 = true := by
  rw [value39, value44, value45, value54, value63, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(196 : Vertex), (205 : Vertex), (220 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (76 : Vertex) [(196 : Vertex), (205 : Vertex), (220 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 8 = true ∨ valuation q 45 = true ∨ valuation q 54 = true ∨ valuation q 63 = true := by
  rw [value8, value44, value45, value54, value63, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(76 : Vertex), (205 : Vertex), (220 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (196 : Vertex) [(76 : Vertex), (205 : Vertex), (220 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 8 = true ∨ valuation q 39 = true ∨ valuation q 45 = true ∨ valuation q 63 = true := by
  rw [value8, value39, value44, value45, value63, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(76 : Vertex), (196 : Vertex), (205 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (220 : Vertex) [(76 : Vertex), (196 : Vertex), (205 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 8 = true ∨ valuation q 39 = true ∨ valuation q 45 = true ∨ valuation q 54 = true := by
  rw [value8, value39, value44, value45, value54, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(76 : Vertex), (196 : Vertex), (205 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (236 : Vertex) [(76 : Vertex), (196 : Vertex), (205 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E260.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112260
