import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value48, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (203 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (200 : Vertex) (203 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 56 = true := by
  rw [value52, value53, value54, value56, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(200 : Vertex), (203 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (194 : Vertex) [(200 : Vertex), (203 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 54 = true ∨ valuation q 56 = true := by
  rw [value48, value53, value54, value56, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(194 : Vertex), (203 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (200 : Vertex) [(194 : Vertex), (203 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 177 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 54 = true := by
  rw [value48, value52, value53, value54, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (202 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(194 : Vertex), (200 : Vertex), (203 : Vertex)] := by decide
  have hg := other_cover q (202 : Vertex) (206 : Vertex) [(194 : Vertex), (200 : Vertex), (203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 36 = false ∨ valuation q 53 = false ∨ valuation q 65 = false := by
  rw [value36, value53, value54, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (202 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 36 = false ∨ valuation q 57 = false ∨ valuation q 65 = false := by
  rw [value36, value54, value57, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (207 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 36 = false ∨ valuation q 65 = false ∨ valuation q 109 = false := by
  rw [value36, value54, value65, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (219 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 65 = false ∨ valuation q 109 = false := by
  rw [value53, value54, value65, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (202 : Vertex) (219 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 65 = false ∨ valuation q 109 = false := by
  rw [value54, value57, value65, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (207 : Vertex) (219 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 53 = true ∨ valuation q 57 = true ∨ valuation q 65 = true ∨ valuation q 109 = true := by
  rw [value53, value54, value57, value65, value109, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(202 : Vertex), (207 : Vertex), (219 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (139 : Vertex) [(202 : Vertex), (207 : Vertex), (219 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 36 = true ∨ valuation q 53 = true ∨ valuation q 57 = true ∨ valuation q 109 = true := by
  rw [value36, value53, value54, value57, value109, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(139 : Vertex), (202 : Vertex), (207 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (219 : Vertex) [(139 : Vertex), (202 : Vertex), (207 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 36 = true ∨ valuation q 53 = true ∨ valuation q 57 = true ∨ valuation q 65 = true := by
  rw [value36, value53, value54, value57, value65, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(139 : Vertex), (202 : Vertex), (207 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (459 : Vertex) [(139 : Vertex), (202 : Vertex), (207 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 37 = false ∨ valuation q 49 = false := by
  rw [value17, value37, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 37 = false ∨ valuation q 52 = false := by
  rw [value17, value37, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 37 = false ∨ valuation q 56 = false := by
  rw [value17, value37, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 37 = false ∨ valuation q 66 = false := by
  rw [value17, value37, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 37 = false ∨ valuation q 110 = false := by
  rw [value17, value37, value55, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value17, value49, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value17, value49, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 49 = false ∨ valuation q 66 = false := by
  rw [value17, value49, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 49 = false ∨ valuation q 110 = false := by
  rw [value17, value49, value55, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value17, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 66 = false := by
  rw [value17, value52, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (200 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 52 = false ∨ valuation q 110 = false := by
  rw [value17, value52, value55, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (200 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 56 = false ∨ valuation q 66 = false := by
  rw [value17, value55, value56, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (206 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 56 = false ∨ valuation q 110 = false := by
  rw [value17, value55, value56, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 17 = false ∨ valuation q 66 = false ∨ valuation q 110 = false := by
  rw [value17, value55, value66, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value37, value49, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (196 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value37, value49, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (196 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 49 = false ∨ valuation q 66 = false := by
  rw [value37, value49, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (196 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 37 = false ∨ valuation q 49 = false ∨ valuation q 110 = false := by
  rw [value37, value49, value55, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (196 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E105.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112105
