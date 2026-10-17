import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value37, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 52 = false ∨ valuation q 66 = false := by
  rw [value37, value52, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (200 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 52 = false ∨ valuation q 110 = false := by
  rw [value37, value52, value55, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (200 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 56 = false ∨ valuation q 66 = false := by
  rw [value37, value55, value56, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 56 = false ∨ valuation q 110 = false := by
  rw [value37, value55, value56, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 66 = false ∨ valuation q 110 = false := by
  rw [value37, value55, value66, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value49, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 66 = false := by
  rw [value49, value52, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (200 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 110 = false := by
  rw [value49, value52, value55, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (200 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 66 = false := by
  rw [value49, value55, value56, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 110 = false := by
  rw [value49, value55, value56, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 49 = false ∨ valuation q 66 = false ∨ valuation q 110 = false := by
  rw [value49, value55, value66, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (196 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 66 = false := by
  rw [value52, value55, value56, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 110 = false := by
  rw [value52, value55, value56, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 66 = false ∨ valuation q 110 = false := by
  rw [value52, value55, value66, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (200 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 66 = false ∨ valuation q 110 = false := by
  rw [value55, value56, value66, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (206 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 112 = true := by
  rw [value19, value51, value53, value55, value56, value57, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ∈ [(78 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (206 : Vertex) [(78 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 19 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value19, value51, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (198 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 112 = false := by
  rw [value51, value53, value56, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (202 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value51, value55, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (204 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 112 = false := by
  rw [value51, value55, value56, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (198 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 112 = false := by
  rw [value53, value55, value56, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (202 : Vertex) (204 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 112 = true := by
  rw [value51, value53, value55, value56, value57, value112, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(198 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (78 : Vertex) [(198 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 19 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 112 = true := by
  rw [value19, value53, value55, value56, value57, value112, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(78 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (198 : Vertex) [(78 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 112 = true := by
  rw [value19, value51, value55, value56, value57, value112, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(78 : Vertex), (198 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (202 : Vertex) [(78 : Vertex), (198 : Vertex), (204 : Vertex), (207 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 57 = true ∨ valuation q 112 = true := by
  rw [value19, value51, value53, value56, value57, value112, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(78 : Vertex), (198 : Vertex), (202 : Vertex), (207 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (204 : Vertex) [(78 : Vertex), (198 : Vertex), (202 : Vertex), (207 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 112 = true := by
  rw [value19, value51, value53, value55, value56, value112, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(78 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (207 : Vertex) [(78 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 180 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value19, value51, value53, value55, value56, value57, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(78 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (462 : Vertex) [(78 : Vertex), (198 : Vertex), (202 : Vertex), (204 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 20 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value20, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (79 : Vertex) (203 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 113 = false := by
  rw [value54, value56, value57, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (203 : Vertex) (206 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 20 = true ∨ valuation q 54 = true ∨ valuation q 113 = true := by
  rw [value20, value54, value57, value113, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(79 : Vertex), (203 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (206 : Vertex) [(79 : Vertex), (203 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 22 = false ∨ valuation q 40 = false ∨ valuation q 59 = false := by
  rw [value22, value40, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (145 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E105.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112105
