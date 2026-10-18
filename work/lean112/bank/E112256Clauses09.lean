import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value8, value39, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 39 = false ∨ valuation q 104 = false := by
  rw [value8, value39, value43, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 170 = true ∨ valuation q 8 = true ∨ valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 52 = true := by
  rw [value8, value39, value40, value43, value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(76 : Vertex), (196 : Vertex), (200 : Vertex), (220 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (460 : Vertex) [(76 : Vertex), (196 : Vertex), (200 : Vertex), (220 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 44 = true := by
  rw [value44, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (207 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = true ∨ valuation q 54 = true := by
  rw [value9, value44, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ∈ [(79 : Vertex), (223 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (207 : Vertex) [(79 : Vertex), (223 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 54 = true := by
  rw [value44, value54, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(223 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (79 : Vertex) [(223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 171 = true ∨ valuation q 9 = true := by
  rw [value9, value44, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (223 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (223 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 45 = true := by
  rw [value45, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (210 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 38 = true ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value38, value45, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ∈ [(194 : Vertex), (211 : Vertex), (218 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (210 : Vertex) [(194 : Vertex), (211 : Vertex), (218 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value38, value45, value46, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (211 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 38 = false ∨ valuation q 51 = false := by
  rw [value38, value51, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (210 : Vertex) (194 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 172 = true ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value45, value46, value51, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(211 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (194 : Vertex) [(211 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 172 = true ∨ valuation q 38 = true ∨ valuation q 51 = true := by
  rw [value38, value45, value51, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(194 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (211 : Vertex) [(194 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 172 = true ∨ valuation q 38 = true ∨ valuation q 46 = true := by
  rw [value38, value45, value46, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(194 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (218 : Vertex) [(194 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 11 = false ∨ valuation q 45 = false ∨ valuation q 49 = false := by
  rw [value11, value45, value46, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (210 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 11 = false ∨ valuation q 45 = false ∨ valuation q 65 = false := by
  rw [value11, value45, value46, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (210 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 11 = false ∨ valuation q 45 = false ∨ valuation q 108 = false := by
  rw [value11, value45, value46, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (210 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 11 = false ∨ valuation q 49 = false ∨ valuation q 65 = false := by
  rw [value11, value46, value49, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (215 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 11 = false ∨ valuation q 49 = false ∨ valuation q 108 = false := by
  rw [value11, value46, value49, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (215 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 11 = false ∨ valuation q 65 = false ∨ valuation q 108 = false := by
  rw [value11, value46, value65, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (83 : Vertex) (243 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 65 = false := by
  rw [value45, value46, value49, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (210 : Vertex) (215 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 108 = false := by
  rw [value45, value46, value49, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (210 : Vertex) (215 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 45 = false ∨ valuation q 65 = false ∨ valuation q 108 = false := by
  rw [value45, value46, value65, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (210 : Vertex) (243 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 65 = false ∨ valuation q 108 = false := by
  rw [value46, value49, value65, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (211 : Vertex) (215 : Vertex) (243 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 12 = true ∨ valuation q 39 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 66 = true := by
  rw [value12, value39, value47, value48, value52, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ∈ [(84 : Vertex), (196 : Vertex), (213 : Vertex), (220 : Vertex), (244 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (212 : Vertex) [(84 : Vertex), (196 : Vertex), (213 : Vertex), (220 : Vertex), (244 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 12 = false ∨ valuation q 39 = false ∨ valuation q 48 = false := by
  rw [value12, value39, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 12 = false ∨ valuation q 39 = false ∨ valuation q 52 = false := by
  rw [value12, value39, value47, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 12 = false ∨ valuation q 48 = false ∨ valuation q 66 = false := by
  rw [value12, value47, value48, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (213 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 39 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 66 = true := by
  rw [value39, value47, value48, value52, value66, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(196 : Vertex), (213 : Vertex), (220 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (84 : Vertex) [(196 : Vertex), (213 : Vertex), (220 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 12 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 66 = true := by
  rw [value12, value47, value48, value52, value66, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(84 : Vertex), (213 : Vertex), (220 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (196 : Vertex) [(84 : Vertex), (213 : Vertex), (220 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 12 = true ∨ valuation q 39 = true ∨ valuation q 52 = true ∨ valuation q 66 = true := by
  rw [value12, value39, value47, value52, value66, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(84 : Vertex), (196 : Vertex), (220 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (213 : Vertex) [(84 : Vertex), (196 : Vertex), (220 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 174 = true ∨ valuation q 12 = true ∨ valuation q 39 = true ∨ valuation q 48 = true ∨ valuation q 66 = true := by
  rw [value12, value39, value47, value48, value66, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (212 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(84 : Vertex), (196 : Vertex), (213 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (212 : Vertex) (220 : Vertex) [(84 : Vertex), (196 : Vertex), (213 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E256.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112256
