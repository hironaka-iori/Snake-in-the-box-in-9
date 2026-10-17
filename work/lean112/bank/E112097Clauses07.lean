import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 89 = false := by
  rw [value54, value55, value56, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (298 : Vertex) (300 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 72 = false ∨ valuation q 89 = false := by
  rw [value54, value56, value72, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (298 : Vertex) (366 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 72 = false ∨ valuation q 89 = false := by
  rw [value55, value56, value72, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (300 : Vertex) (366 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 179 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 72 = true ∨ valuation q 89 = true := by
  rw [value50, value55, value56, value72, value89, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (298 : Vertex) → w ∈ [(294 : Vertex), (300 : Vertex), (366 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (298 : Vertex) [(294 : Vertex), (300 : Vertex), (366 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 92 = false := by
  rw [value57, value58, value62, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (307 : Vertex) (313 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 92 = false := by
  rw [value57, value60, value62, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (309 : Vertex) (313 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 180 = true ∨ valuation q 60 = true ∨ valuation q 62 = true ∨ valuation q 92 = true := by
  rw [value57, value60, value62, value92, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(309 : Vertex), (313 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(309 : Vertex), (313 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 180 = true ∨ valuation q 58 = true ∨ valuation q 62 = true ∨ valuation q 92 = true := by
  rw [value57, value58, value62, value92, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (309 : Vertex) → w ∈ [(307 : Vertex), (313 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (309 : Vertex) [(307 : Vertex), (313 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 180 = true ∨ valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 92 = true := by
  rw [value57, value58, value60, value92, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (313 : Vertex) → w ∈ [(307 : Vertex), (309 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (313 : Vertex) [(307 : Vertex), (309 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 180 = true ∨ valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value57, value58, value60, value62, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(307 : Vertex), (309 : Vertex), (313 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (433 : Vertex) [(307 : Vertex), (309 : Vertex), (313 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value10, value57, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (305 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 57 = false ∨ valuation q 64 = false := by
  rw [value10, value57, value58, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (305 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 57 = false ∨ valuation q 76 = false := by
  rw [value10, value57, value58, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (305 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value10, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (311 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 61 = false ∨ valuation q 76 = false := by
  rw [value10, value58, value61, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (311 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value10, value58, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (311 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 64 = false ∨ valuation q 76 = false := by
  rw [value10, value58, value64, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (315 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 10 = false ∨ valuation q 64 = false ∨ valuation q 94 = false := by
  rw [value10, value58, value64, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (51 : Vertex) (315 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value57, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (305 : Vertex) (311 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 76 = false := by
  rw [value57, value58, value61, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (305 : Vertex) (311 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value57, value58, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (305 : Vertex) (311 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 76 = false := by
  rw [value57, value58, value64, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (305 : Vertex) (315 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 76 = false := by
  rw [value58, value61, value64, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (311 : Vertex) (315 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 94 = false := by
  rw [value58, value61, value64, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (311 : Vertex) (315 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 76 = false ∨ valuation q 94 = false := by
  rw [value58, value61, value76, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (311 : Vertex) (371 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 76 = false ∨ valuation q 94 = false := by
  rw [value58, value64, value76, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (307 : Vertex) (315 : Vertex) (371 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 11 = false ∨ valuation q 49 = false ∨ valuation q 60 = false := by
  rw [value11, value49, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (292 : Vertex) (309 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 11 = false ∨ valuation q 49 = false ∨ valuation q 77 = false := by
  rw [value11, value49, value59, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (292 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 11 = false ∨ valuation q 60 = false ∨ valuation q 77 = false := by
  rw [value11, value59, value60, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (52 : Vertex) (309 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 77 = false := by
  rw [value49, value59, value60, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (292 : Vertex) (309 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 182 = true ∨ valuation q 11 = true ∨ valuation q 49 = true ∨ valuation q 77 = true := by
  rw [value11, value49, value59, value77, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (309 : Vertex) → w ∈ [(52 : Vertex), (292 : Vertex), (372 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (309 : Vertex) [(52 : Vertex), (292 : Vertex), (372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value57, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (309 : Vertex) (305 : Vertex) (308 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E097.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112097
