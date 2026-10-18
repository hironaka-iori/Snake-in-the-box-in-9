import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 88 = false := by
  rw [value47, value48, value50, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (260 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value47, value50, value51, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (263 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value47, value50, value51, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (263 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 88 = false := by
  rw [value47, value50, value51, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (263 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value47, value50, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (270 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 56 = false ∨ valuation q 88 = false := by
  rw [value47, value50, value56, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (270 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 47 = false ∨ valuation q 70 = false ∨ valuation q 88 = false := by
  rw [value47, value50, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (326 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value48, value50, value51, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value48, value50, value51, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 88 = false := by
  rw [value48, value50, value51, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (263 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value48, value50, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (270 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 88 = false := by
  rw [value48, value50, value56, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (270 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 70 = false ∨ valuation q 88 = false := by
  rw [value48, value50, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (326 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value50, value51, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (263 : Vertex) (270 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 88 = false := by
  rw [value50, value51, value56, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (263 : Vertex) (270 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 70 = false ∨ valuation q 88 = false := by
  rw [value50, value51, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (263 : Vertex) (326 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 70 = false ∨ valuation q 88 = false := by
  rw [value50, value56, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (270 : Vertex) (326 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 57 = false := by
  rw [value49, value50, value51, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 71 = false := by
  rw [value49, value50, value51, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (262 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value49, value51, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (261 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 62 = false := by
  rw [value50, value51, value57, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 89 = false := by
  rw [value50, value51, value57, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (271 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 62 = false ∨ valuation q 71 = false := by
  rw [value50, value51, value62, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 62 = false ∨ valuation q 89 = false := by
  rw [value50, value51, value62, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 57 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value51, value57, value71, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (271 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 71 = false ∨ valuation q 89 = false := by
  rw [value51, value62, value71, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (279 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 168 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 57 = true ∨ valuation q 62 = true ∨ valuation q 89 = true := by
  rw [value49, value50, value51, value57, value62, value89, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (327 : Vertex) [(261 : Vertex), (262 : Vertex), (271 : Vertex), (279 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value4, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value4, value52, value53, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 72 = false := by
  rw [value4, value52, value53, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value4, value52, value53, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (266 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 55 = false ∨ valuation q 72 = false := by
  rw [value4, value52, value55, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (8 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E203.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112203
