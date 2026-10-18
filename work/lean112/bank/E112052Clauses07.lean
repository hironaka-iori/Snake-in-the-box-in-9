import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 61 = true := by
  rw [value50, value51, value55, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (257 : Vertex) [(258 : Vertex), (267 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 55 = true ∨ valuation q 61 = true := by
  rw [value49, value51, value55, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(257 : Vertex), (267 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 61 = true := by
  rw [value49, value50, value51, value61, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(257 : Vertex), (258 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(257 : Vertex), (258 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value49, value50, value51, value55, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(257 : Vertex), (258 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (275 : Vertex) [(257 : Vertex), (258 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 68 = false := by
  rw [value52, value53, value56, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (324 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 87 = false := by
  rw [value52, value53, value56, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 68 = false ∨ valuation q 87 = false := by
  rw [value52, value53, value68, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (324 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 68 = false ∨ valuation q 87 = false := by
  rw [value52, value56, value68, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (268 : Vertex) (324 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 49 = false ∨ valuation q 69 = false ∨ valuation q 88 = false := by
  rw [value49, value53, value69, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 57 = false ∨ valuation q 69 = false := by
  rw [value52, value53, value57, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (269 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 88 = true := by
  rw [value52, value53, value57, value69, value88, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(260 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 88 = true := by
  rw [value49, value53, value57, value69, value88, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(257 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (260 : Vertex) [(257 : Vertex), (269 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 69 = true ∨ valuation q 88 = true := by
  rw [value49, value52, value53, value69, value88, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (269 : Vertex) [(257 : Vertex), (260 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 88 = true := by
  rw [value49, value52, value53, value57, value88, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (269 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (325 : Vertex) [(257 : Vertex), (260 : Vertex), (269 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 180 = true ∨ valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 69 = true := by
  rw [value49, value52, value53, value57, value69, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(257 : Vertex), (260 : Vertex), (269 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (389 : Vertex) [(257 : Vertex), (260 : Vertex), (269 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 49 = false ∨ valuation q 55 = false ∨ valuation q 92 = false := by
  rw [value49, value54, value55, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (257 : Vertex) (267 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 92 = false := by
  rw [value54, value55, value57, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (267 : Vertex) (269 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 92 = true := by
  rw [value54, value55, value57, value92, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(267 : Vertex), (269 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (257 : Vertex) [(267 : Vertex), (269 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 92 = true := by
  rw [value49, value54, value57, value92, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(257 : Vertex), (269 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (267 : Vertex) [(257 : Vertex), (269 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 55 = true ∨ valuation q 92 = true := by
  rw [value49, value54, value55, value92, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (269 : Vertex) [(257 : Vertex), (267 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value49, value54, value55, value57, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex), (269 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (393 : Vertex) [(257 : Vertex), (267 : Vertex), (269 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 94 = false := by
  rw [value51, value54, value55, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value51, value54, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (267 : Vertex) (259 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 54 = true ∨ valuation q 94 = true := by
  rw [value54, value55, value94, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(265 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (259 : Vertex) [(265 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 182 = true ∨ valuation q 51 = true ∨ valuation q 94 = true := by
  rw [value51, value55, value94, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(259 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (265 : Vertex) [(259 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 58 = false ∨ valuation q 74 = false := by
  rw [value52, value56, value58, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (270 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value52, value56, value64, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 64 = false := by
  rw [value56, value57, value58, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (269 : Vertex) (270 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 74 = false := by
  rw [value56, value57, value58, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (269 : Vertex) (270 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value56, value57, value64, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (269 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value56, value58, value64, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (270 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 183 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 64 = true ∨ valuation q 74 = true := by
  rw [value52, value56, value57, value64, value74, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (284 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (269 : Vertex), (284 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E052.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112052
