import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 77 = false ∨ valuation q 96 = false := by
  rw [value58, value59, value77, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (275 : Vertex) (337 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 77 = false := by
  rw [value58, value61, value64, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (277 : Vertex) (281 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 77 = false ∨ valuation q 96 = false := by
  rw [value58, value64, value77, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (281 : Vertex) (337 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 58 = false ∨ valuation q 62 = false := by
  rw [value10, value58, value59, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (273 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 58 = false ∨ valuation q 66 = false := by
  rw [value10, value58, value59, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (273 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 58 = false ∨ valuation q 79 = false := by
  rw [value10, value58, value59, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (273 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 58 = false ∨ valuation q 98 = false := by
  rw [value10, value58, value59, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (273 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value10, value59, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (279 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 62 = false ∨ valuation q 79 = false := by
  rw [value10, value59, value62, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (279 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 62 = false ∨ valuation q 98 = false := by
  rw [value10, value59, value62, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (279 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 66 = false ∨ valuation q 79 = false := by
  rw [value10, value59, value66, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (283 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 10 = false ∨ valuation q 66 = false ∨ valuation q 98 = false := by
  rw [value10, value59, value66, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (19 : Vertex) (283 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 66 = false := by
  rw [value58, value59, value62, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (273 : Vertex) (279 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 79 = false := by
  rw [value58, value59, value62, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (273 : Vertex) (279 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 98 = false := by
  rw [value58, value59, value62, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (273 : Vertex) (279 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 58 = false ∨ valuation q 66 = false ∨ valuation q 98 = false := by
  rw [value58, value59, value66, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (273 : Vertex) (283 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 79 = false := by
  rw [value59, value62, value66, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (279 : Vertex) (283 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 98 = false := by
  rw [value59, value62, value66, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (279 : Vertex) (283 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 60 = true := by
  rw [value60, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (276 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 48 = true ∨ valuation q 61 = true := by
  rw [value48, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (277 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (276 : Vertex) [(260 : Vertex), (277 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 48 = false ∨ valuation q 61 = false := by
  rw [value48, value61, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (276 : Vertex) (260 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 177 = true ∨ valuation q 61 = true := by
  rw [value60, value61, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (260 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 177 = true ∨ valuation q 48 = true := by
  rw [value48, value60, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value49, value58, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (273 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 49 = false ∨ valuation q 58 = false ∨ valuation q 62 = false := by
  rw [value49, value58, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (273 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value49, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value58, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (273 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value58, value60, value61, value62, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(273 : Vertex), (276 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (261 : Vertex) [(273 : Vertex), (276 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 58 = true ∨ valuation q 62 = true := by
  rw [value49, value58, value61, value62, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (273 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (276 : Vertex) [(261 : Vertex), (273 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value49, value58, value60, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(261 : Vertex), (273 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (279 : Vertex) [(261 : Vertex), (273 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 51 = true ∨ valuation q 59 = true ∨ valuation q 61 = true ∨ valuation q 67 = true := by
  rw [value51, value59, value61, value62, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ∈ [(263 : Vertex), (275 : Vertex), (277 : Vertex), (287 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (279 : Vertex) [(263 : Vertex), (275 : Vertex), (277 : Vertex), (287 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 179 = true ∨ valuation q 59 = true ∨ valuation q 61 = true ∨ valuation q 67 = true := by
  rw [value59, value61, value62, value67, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(275 : Vertex), (277 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (263 : Vertex) [(275 : Vertex), (277 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E207.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112207
