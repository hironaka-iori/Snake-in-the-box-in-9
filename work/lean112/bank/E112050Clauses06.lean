import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 183 = true ∨ valuation q 51 = true ∨ valuation q 95 = true := by
  rw [value51, value55, value95, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(259 : Vertex), (395 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (265 : Vertex) [(259 : Vertex), (395 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 75 = false := by
  rw [value52, value56, value64, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (260 : Vertex) (284 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 75 = false := by
  rw [value56, value57, value58, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (268 : Vertex) (269 : Vertex) (270 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 64 = true ∨ valuation q 75 = true := by
  rw [value56, value57, value58, value64, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(269 : Vertex), (270 : Vertex), (284 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (260 : Vertex) [(269 : Vertex), (270 : Vertex), (284 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 64 = true ∨ valuation q 75 = true := by
  rw [value52, value56, value57, value64, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (284 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (269 : Vertex), (284 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 75 = true := by
  rw [value52, value56, value57, value58, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (270 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (284 : Vertex) [(260 : Vertex), (269 : Vertex), (270 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 184 = true ∨ valuation q 52 = true ∨ valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 64 = true := by
  rw [value52, value56, value57, value58, value64, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(260 : Vertex), (269 : Vertex), (270 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (332 : Vertex) [(260 : Vertex), (269 : Vertex), (270 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value53, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 65 = false := by
  rw [value53, value54, value57, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 96 = false := by
  rw [value53, value54, value57, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (265 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value53, value56, value57, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 96 = false := by
  rw [value53, value56, value57, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 53 = false ∨ valuation q 65 = false ∨ valuation q 96 = false := by
  rw [value53, value57, value65, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (285 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value54, value56, value57, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 96 = false := by
  rw [value54, value56, value57, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (268 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 54 = false ∨ valuation q 65 = false ∨ valuation q 96 = false := by
  rw [value54, value57, value65, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (265 : Vertex) (285 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 65 = false ∨ valuation q 96 = false := by
  rw [value56, value57, value65, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (285 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 185 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 65 = true ∨ valuation q 96 = true := by
  rw [value53, value56, value57, value65, value96, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(261 : Vertex), (268 : Vertex), (285 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (265 : Vertex) [(261 : Vertex), (268 : Vertex), (285 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 66 = false ∨ valuation q 97 = false := by
  rw [value56, value58, value66, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (268 : Vertex) (286 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 186 = true ∨ valuation q 66 = true ∨ valuation q 97 = true := by
  rw [value58, value66, value97, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(286 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (268 : Vertex) [(286 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 186 = true ∨ valuation q 56 = true ∨ valuation q 97 = true := by
  rw [value56, value58, value97, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(268 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (286 : Vertex) [(268 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = true ∨ valuation q 63 = true := by
  rw [value59, value60, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ∈ [(274 : Vertex), (280 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (272 : Vertex) [(274 : Vertex), (280 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 60 = false ∨ valuation q 63 = false := by
  rw [value60, value63, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (272 : Vertex) (274 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 187 = true ∨ valuation q 63 = true := by
  rw [value59, value63, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(280 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (274 : Vertex) [(280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 50 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value50, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (258 : Vertex) (272 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 188 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value59, value60, value61, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(272 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (258 : Vertex) [(272 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 188 = true ∨ valuation q 50 = true ∨ valuation q 61 = true := by
  rw [value50, value60, value61, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(258 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (272 : Vertex) [(258 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 188 = true ∨ valuation q 50 = true ∨ valuation q 59 = true := by
  rw [value50, value59, value60, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(258 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (275 : Vertex) [(258 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value51, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (275 : Vertex) (259 : Vertex) (274 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 51 = false ∨ valuation q 60 = false := by
  rw [value51, value60, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (275 : Vertex) (259 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 189 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value60, value61, value62, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(274 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (259 : Vertex) [(274 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 189 = true ∨ valuation q 51 = true ∨ valuation q 62 = true := by
  rw [value51, value61, value62, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(259 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (274 : Vertex) [(259 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E050.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112050
