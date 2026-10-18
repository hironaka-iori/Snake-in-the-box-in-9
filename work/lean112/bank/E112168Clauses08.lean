import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 104 = false := by
  rw [value50, value52, value62, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (206 : Vertex) (220 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 63 = false := by
  rw [value46, value48, value51, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (201 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value48, value51, value53, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (201 : Vertex) (207 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 165 = true ∨ valuation q 46 = true ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 63 = true := by
  rw [value46, value50, value51, value53, value63, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(197 : Vertex), (204 : Vertex), (207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (201 : Vertex) [(197 : Vertex), (204 : Vertex), (207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 165 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 63 = true := by
  rw [value46, value48, value50, value51, value63, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(197 : Vertex), (201 : Vertex), (204 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (207 : Vertex) [(197 : Vertex), (201 : Vertex), (204 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 165 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value46, value48, value50, value51, value53, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(197 : Vertex), (201 : Vertex), (204 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [(197 : Vertex), (201 : Vertex), (204 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 49 = false ∨ valuation q 64 = false := by
  rw [value13, value49, value52, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (202 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 50 = false ∨ valuation q 64 = false := by
  rw [value13, value50, value52, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (204 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 53 = false ∨ valuation q 64 = false := by
  rw [value13, value52, value53, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (207 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 13 = false ∨ valuation q 64 = false ∨ valuation q 105 = false := by
  rw [value13, value52, value64, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (206 : Vertex) (78 : Vertex) (222 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value47, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value47, value51, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (207 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 167 = true ∨ valuation q 51 = true ∨ valuation q 52 = true := by
  rw [value51, value52, value53, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(205 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (199 : Vertex) [(205 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 167 = true ∨ valuation q 47 = true ∨ valuation q 52 = true := by
  rw [value47, value52, value53, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(199 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [(199 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 168 = true ∨ valuation q 14 = true ∨ valuation q 33 = true ∨ valuation q 42 = true ∨ valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 59 = true := by
  rw [value14, value33, value42, value54, value55, value56, value59, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(80 : Vertex), (144 : Vertex), (192 : Vertex), (209 : Vertex), (210 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (464 : Vertex) [(80 : Vertex), (144 : Vertex), (192 : Vertex), (209 : Vertex), (210 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 43 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value43, value54, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (208 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 43 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value43, value54, value55, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (208 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 43 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value43, value55, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (211 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value54, value55, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (208 : Vertex) (211 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value54, value57, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (209 : Vertex) (208 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 169 = true ∨ valuation q 43 = true ∨ valuation q 57 = true ∨ valuation q 60 = true := by
  rw [value43, value55, value57, value60, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(193 : Vertex), (211 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (208 : Vertex) [(193 : Vertex), (211 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 169 = true ∨ valuation q 43 = true ∨ valuation q 54 = true ∨ valuation q 60 = true := by
  rw [value43, value54, value55, value60, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(193 : Vertex), (208 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (211 : Vertex) [(193 : Vertex), (208 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value44, value54, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 58 = false := by
  rw [value44, value54, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 61 = false := by
  rw [value44, value54, value56, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 44 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value44, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (211 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 44 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value44, value56, value57, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (211 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value54, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (208 : Vertex) (211 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value54, value56, value57, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (208 : Vertex) (211 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value54, value56, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (208 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 61 = false := by
  rw [value56, value57, value58, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (211 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 171 = true ∨ valuation q 55 = true ∨ valuation q 56 = true := by
  rw [value55, value56, value57, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(209 : Vertex), (210 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (195 : Vertex) [(209 : Vertex), (210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E168.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112168
