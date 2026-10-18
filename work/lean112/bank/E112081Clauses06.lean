import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 69 = false := by
  rw [value46, value49, value53, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (260 : Vertex) (264 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 87 = false := by
  rw [value46, value49, value53, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (260 : Vertex) (264 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 69 = false ∨ valuation q 87 = false := by
  rw [value46, value49, value69, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (260 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 87 = false := by
  rw [value46, value53, value69, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (264 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 2 = false ∨ valuation q 50 = false ∨ valuation q 70 = false := by
  rw [value2, value47, value50, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (261 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 2 = false ∨ valuation q 59 = false ∨ valuation q 70 = false := by
  rw [value2, value47, value59, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (273 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 2 = false ∨ valuation q 59 = false ∨ valuation q 88 = false := by
  rw [value2, value47, value59, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (273 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 2 = false ∨ valuation q 70 = false ∨ valuation q 88 = false := by
  rw [value2, value47, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (1 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = false ∨ valuation q 59 = false ∨ valuation q 88 = false := by
  rw [value46, value47, value59, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (256 : Vertex) (273 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 59 = false ∨ valuation q 70 = false := by
  rw [value47, value50, value59, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (273 : Vertex) (321 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 59 = false ∨ valuation q 70 = false ∨ valuation q 88 = false := by
  rw [value47, value59, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (273 : Vertex) (321 : Vertex) (385 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 164 = true ∨ valuation q 2 = true ∨ valuation q 46 = true ∨ valuation q 50 = true ∨ valuation q 59 = true ∨ valuation q 88 = true := by
  rw [value2, value46, value47, value50, value59, value88, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(1 : Vertex), (256 : Vertex), (261 : Vertex), (273 : Vertex), (385 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (321 : Vertex) [(1 : Vertex), (256 : Vertex), (261 : Vertex), (273 : Vertex), (385 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value46, value48, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (256 : Vertex) (262 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 51 = true ∨ valuation q 54 = true := by
  rw [value48, value51, value54, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (256 : Vertex) → w ∈ [(262 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (256 : Vertex) [(262 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 46 = true ∨ valuation q 54 = true := by
  rw [value46, value48, value54, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(256 : Vertex), (266 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (262 : Vertex) [(256 : Vertex), (266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 46 = true ∨ valuation q 51 = true := by
  rw [value46, value48, value51, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(256 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(256 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 61 = false := by
  rw [value46, value49, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (262 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 61 = false := by
  rw [value46, value49, value56, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 166 = true ∨ valuation q 46 = true ∨ valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 61 = true := by
  rw [value46, value49, value50, value51, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(256 : Vertex), (261 : Vertex), (262 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (268 : Vertex) [(256 : Vertex), (261 : Vertex), (262 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 166 = true ∨ valuation q 46 = true ∨ valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 56 = true := by
  rw [value46, value49, value50, value51, value56, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(256 : Vertex), (261 : Vertex), (262 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (276 : Vertex) [(256 : Vertex), (261 : Vertex), (262 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value47, value49, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 62 = false := by
  rw [value47, value49, value50, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (260 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value47, value50, value52, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (263 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value49, value50, value52, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (263 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 47 = true ∨ valuation q 49 = true ∨ valuation q 52 = true := by
  rw [value47, value49, value50, value52, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (277 : Vertex) [(257 : Vertex), (260 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value3, value48, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (260 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value3, value48, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 57 = false := by
  rw [value3, value48, value51, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 71 = false := by
  rw [value3, value48, value51, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 89 = false := by
  rw [value3, value48, value51, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value3, value49, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (260 : Vertex) (263 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 3 = false ∨ valuation q 49 = false ∨ valuation q 57 = false := by
  rw [value3, value49, value51, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (260 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E081.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112081
