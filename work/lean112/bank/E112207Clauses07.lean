import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value45, value47, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (256 : Vertex) (262 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 164 = true ∨ valuation q 45 = true ∨ valuation q 53 = true := by
  rw [value45, value47, value53, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(256 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (262 : Vertex) [(256 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 164 = true ∨ valuation q 45 = true ∨ valuation q 50 = true := by
  rw [value45, value47, value50, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(256 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(256 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value45, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (261 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value45, value48, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (261 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 60 = false := by
  rw [value45, value48, value49, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (261 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value45, value48, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (262 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 60 = false := by
  rw [value45, value48, value50, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (262 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value45, value48, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value48, value49, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 60 = false := by
  rw [value48, value49, value50, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value48, value49, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 60 = false := by
  rw [value48, value50, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 60 = true := by
  rw [value45, value48, value50, value55, value60, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(256 : Vertex), (262 : Vertex), (268 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (261 : Vertex) [(256 : Vertex), (262 : Vertex), (268 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 55 = true ∨ valuation q 60 = true := by
  rw [value45, value48, value49, value55, value60, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(256 : Vertex), (261 : Vertex), (268 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (262 : Vertex) [(256 : Vertex), (261 : Vertex), (268 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value45, value48, value49, value50, value55, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(256 : Vertex), (261 : Vertex), (262 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (276 : Vertex) [(256 : Vertex), (261 : Vertex), (262 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 61 = true ∨ valuation q 87 = true := by
  rw [value46, value48, value49, value51, value61, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ∈ [(257 : Vertex), (260 : Vertex), (263 : Vertex), (277 : Vertex), (389 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (261 : Vertex) [(257 : Vertex), (260 : Vertex), (263 : Vertex), (277 : Vertex), (389 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value46, value49, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (263 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 166 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 61 = true ∨ valuation q 87 = true := by
  rw [value46, value48, value49, value61, value87, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (277 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (263 : Vertex) [(257 : Vertex), (260 : Vertex), (277 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 166 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 87 = true := by
  rw [value46, value48, value49, value51, value87, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (263 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (277 : Vertex) [(257 : Vertex), (260 : Vertex), (263 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 166 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 61 = true := by
  rw [value46, value48, value49, value51, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (263 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (389 : Vertex) [(257 : Vertex), (260 : Vertex), (263 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value3, value47, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (260 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value3, value47, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 88 = false := by
  rw [value3, value47, value50, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 51 = false := by
  rw [value3, value48, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value3, value48, value50, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (260 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 88 = false := by
  rw [value3, value48, value50, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (260 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value3, value50, value51, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (263 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value3, value50, value51, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (263 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 51 = false ∨ valuation q 88 = false := by
  rw [value3, value50, value51, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (263 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value3, value50, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (270 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 88 = false := by
  rw [value3, value50, value56, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (270 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E207.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112207
