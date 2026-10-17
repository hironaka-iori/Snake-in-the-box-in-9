import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 174 = true ∨ valuation q 41 = true ∨ valuation q 47 = true ∨ valuation q 124 = true := by
  rw [value41, value46, value47, value124, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(240 : Vertex), (252 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(240 : Vertex), (252 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 174 = true ∨ valuation q 27 = true ∨ valuation q 47 = true ∨ valuation q 124 = true := by
  rw [value27, value46, value47, value124, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(184 : Vertex), (252 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (240 : Vertex) [(184 : Vertex), (252 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 174 = true ∨ valuation q 27 = true ∨ valuation q 41 = true ∨ valuation q 124 = true := by
  rw [value27, value41, value46, value124, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(184 : Vertex), (240 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (252 : Vertex) [(184 : Vertex), (240 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 174 = true ∨ valuation q 27 = true ∨ valuation q 41 = true ∨ valuation q 47 = true := by
  rw [value27, value41, value46, value47, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(184 : Vertex), (240 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (504 : Vertex) [(184 : Vertex), (240 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value44, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (252 : Vertex) (244 : Vertex) (248 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 175 = true ∨ valuation q 44 = true ∨ valuation q 46 = true := by
  rw [value44, value46, value47, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(244 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (254 : Vertex) [(244 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 49 = false := by
  rw [value45, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (246 : Vertex) (252 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 49 = true := by
  rw [value47, value48, value49, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(252 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (246 : Vertex) [(252 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 176 = true ∨ valuation q 45 = true ∨ valuation q 49 = true := by
  rw [value45, value48, value49, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(246 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (252 : Vertex) [(246 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 176 = true ∨ valuation q 45 = true ∨ valuation q 47 = true := by
  rw [value45, value47, value48, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(246 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (255 : Vertex) [(246 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 40 = true ∨ valuation q 48 = true := by
  rw [value40, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ∈ [(239 : Vertex), (254 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (255 : Vertex) [(239 : Vertex), (254 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 177 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(254 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (239 : Vertex) [(254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 177 = true ∨ valuation q 40 = true := by
  rw [value40, value49, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(239 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (254 : Vertex) [(239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value50, value51, value52, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (290 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value50, value51, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (292 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 86 = false := by
  rw [value50, value51, value53, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (292 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 86 = false := by
  rw [value50, value51, value56, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 86 = false := by
  rw [value50, value52, value53, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (290 : Vertex) (292 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 56 = false ∨ valuation q 86 = false := by
  rw [value50, value52, value56, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (290 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 1 = false ∨ valuation q 54 = false ∨ valuation q 87 = false := by
  rw [value1, value51, value54, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (289 : Vertex) (33 : Vertex) (293 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 179 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 87 = true := by
  rw [value50, value51, value54, value87, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (289 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(288 : Vertex), (293 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (289 : Vertex) (33 : Vertex) [(288 : Vertex), (293 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 69 = false := by
  rw [value52, value55, value57, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (290 : Vertex) (294 : Vertex) (298 : Vertex) (354 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 180 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 88 = true := by
  rw [value52, value55, value57, value69, value88, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(294 : Vertex), (298 : Vertex), (354 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (288 : Vertex) [(294 : Vertex), (298 : Vertex), (354 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 180 = true ∨ valuation q 50 = true ∨ valuation q 57 = true ∨ valuation q 69 = true ∨ valuation q 88 = true := by
  rw [value50, value52, value57, value69, value88, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (294 : Vertex) → w ∈ [(288 : Vertex), (298 : Vertex), (354 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (294 : Vertex) [(288 : Vertex), (298 : Vertex), (354 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 180 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 88 = true := by
  rw [value50, value52, value55, value57, value88, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (290 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(288 : Vertex), (294 : Vertex), (298 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (290 : Vertex) (354 : Vertex) [(288 : Vertex), (294 : Vertex), (298 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value50, value53, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (292 : Vertex) (288 : Vertex) (294 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value53, value54, value55, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (292 : Vertex) (293 : Vertex) (294 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 71 = false := by
  rw [value53, value54, value55, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (292 : Vertex) (293 : Vertex) (294 : Vertex) (356 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value53, value54, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (292 : Vertex) (293 : Vertex) (294 : Vertex) (420 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 3 = false ∨ valuation q 53 = false ∨ valuation q 61 = false := by
  rw [value3, value53, value54, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (37 : Vertex) (292 : Vertex) (309 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 3 = false ∨ valuation q 61 = false ∨ valuation q 72 = false := by
  rw [value3, value54, value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (37 : Vertex) (309 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 61 = false := by
  rw [value51, value53, value54, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (293 : Vertex) (289 : Vertex) (292 : Vertex) (309 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E034.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112034
