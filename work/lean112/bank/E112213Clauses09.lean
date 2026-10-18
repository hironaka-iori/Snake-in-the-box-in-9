import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 160 = true ∨ valuation q 39 = true ∨ valuation q 44 = true ∨ valuation q 62 = true := by
  rw [value39, value43, value44, value62, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(129 : Vertex), (141 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(129 : Vertex), (141 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true ∨ valuation q 45 = true ∨ valuation q 53 = true := by
  rw [value44, value45, value53, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(143 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (137 : Vertex) [(143 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true ∨ valuation q 43 = true ∨ valuation q 53 = true := by
  rw [value43, value44, value53, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(137 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (143 : Vertex) [(137 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 161 = true ∨ valuation q 43 = true ∨ valuation q 45 = true := by
  rw [value43, value44, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(137 : Vertex), (143 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (157 : Vertex) [(137 : Vertex), (143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 42 = false ∨ valuation q 44 = false ∨ valuation q 55 = false := by
  rw [value42, value44, value45, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (135 : Vertex) (141 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 38 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value38, value46, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (128 : Vertex) (145 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 163 = true ∨ valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 50 = true := by
  rw [value46, value47, value48, value50, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(145 : Vertex), (146 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (128 : Vertex) [(145 : Vertex), (146 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 163 = true ∨ valuation q 38 = true ∨ valuation q 48 = true ∨ valuation q 50 = true := by
  rw [value38, value46, value48, value50, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(128 : Vertex), (146 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (145 : Vertex) [(128 : Vertex), (146 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 163 = true ∨ valuation q 38 = true ∨ valuation q 47 = true ∨ valuation q 48 = true := by
  rw [value38, value46, value47, value48, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(128 : Vertex), (145 : Vertex), (146 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (148 : Vertex) [(128 : Vertex), (145 : Vertex), (146 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 39 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value39, value46, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (129 : Vertex) (144 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 164 = true ∨ valuation q 39 = true ∨ valuation q 49 = true := by
  rw [value39, value47, value49, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(129 : Vertex), (147 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (144 : Vertex) [(129 : Vertex), (147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value8, value40, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (130 : Vertex) (144 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 40 = false ∨ valuation q 49 = false := by
  rw [value8, value40, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (130 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value8, value40, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (130 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 40 = false ∨ valuation q 66 = false := by
  rw [value8, value40, value48, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (130 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 40 = false ∨ valuation q 94 = false := by
  rw [value8, value40, value48, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (130 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value8, value46, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (144 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value8, value46, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (144 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 66 = false := by
  rw [value8, value46, value48, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (144 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 94 = false := by
  rw [value8, value46, value48, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (144 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value8, value48, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (147 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 49 = false ∨ valuation q 66 = false := by
  rw [value8, value48, value49, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (147 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 49 = false ∨ valuation q 94 = false := by
  rw [value8, value48, value49, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (147 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 51 = false ∨ valuation q 66 = false := by
  rw [value8, value48, value51, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (154 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 51 = false ∨ valuation q 94 = false := by
  rw [value8, value48, value51, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (154 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 8 = false ∨ valuation q 66 = false ∨ valuation q 94 = false := by
  rw [value8, value48, value66, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (18 : Vertex) (210 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 49 = false := by
  rw [value40, value46, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (144 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value40, value46, value48, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (144 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 66 = false := by
  rw [value40, value46, value48, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (144 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 94 = false := by
  rw [value40, value46, value48, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (144 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value40, value48, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (147 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 66 = false := by
  rw [value40, value48, value49, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (146 : Vertex) (130 : Vertex) (147 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E213.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112213
