import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 117 = false := by
  rw [value50, value51, value52, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (250 : Vertex) (252 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 3 = false ∨ valuation q 55 = false ∨ valuation q 58 = false := by
  rw [value3, value53, value55, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (270 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 55 = true ∨ valuation q 58 = true := by
  rw [value53, value55, value58, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(270 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (6 : Vertex) [(270 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 3 = true ∨ valuation q 55 = true := by
  rw [value3, value53, value55, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(6 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (278 : Vertex) [(6 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true := by
  rw [value54, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (264 : Vertex) (280 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 64 = true := by
  rw [value55, value64, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(302 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (262 : Vertex) [(302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 53 = true := by
  rw [value53, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(262 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (302 : Vertex) [(262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 61 = true := by
  rw [value56, value61, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [(282 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (278 : Vertex) [(282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 174 = true ∨ valuation q 58 = true := by
  rw [value56, value58, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(278 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (282 : Vertex) [(278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 175 = true := by
  rw [value57, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (278 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (276 : Vertex) (278 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 56 = true ∨ valuation q 57 = true := by
  rw [value56, value57, value58, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (262 : Vertex) [(274 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 176 = true ∨ valuation q 53 = true ∨ valuation q 57 = true := by
  rw [value53, value57, value58, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(262 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (274 : Vertex) [(262 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 177 = true ∨ valuation q 54 = true ∨ valuation q 61 = true := by
  rw [value54, value59, value61, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(264 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (281 : Vertex) [(264 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 177 = true ∨ valuation q 54 = true ∨ valuation q 60 = true := by
  rw [value54, value59, value60, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(264 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (282 : Vertex) [(264 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 178 = true ∨ valuation q 62 = true := by
  rw [value60, value62, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(285 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (280 : Vertex) [(285 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 178 = true ∨ valuation q 59 = true := by
  rw [value59, value60, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (285 : Vertex) → w ∈ [(280 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (285 : Vertex) [(280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 59 = true := by
  rw [value59, value61, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(280 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (274 : Vertex) [(280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 56 = true := by
  rw [value56, value61, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (280 : Vertex) [(274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 180 = true ∨ valuation q 66 = true := by
  rw [value62, value66, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(317 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (281 : Vertex) [(317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 55 = false ∨ valuation q 67 = false ∨ valuation q 74 = false := by
  rw [value55, value64, value67, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (270 : Vertex) (318 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 55 = false ∨ valuation q 67 = false ∨ valuation q 90 = false := by
  rw [value55, value64, value67, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (270 : Vertex) (318 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 55 = false ∨ valuation q 74 = false ∨ valuation q 90 = false := by
  rw [value55, value64, value74, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (270 : Vertex) (366 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 74 = false ∨ valuation q 90 = false := by
  rw [value64, value67, value74, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (318 : Vertex) (366 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 183 = true ∨ valuation q 66 = true := by
  rw [value65, value66, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(317 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (318 : Vertex) [(317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 83 = false := by
  rw [value62, value65, value66, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (285 : Vertex) (316 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 100 = false := by
  rw [value62, value65, value66, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (285 : Vertex) (316 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 83 = false ∨ valuation q 100 = false := by
  rw [value62, value66, value83, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (285 : Vertex) (381 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 65 = false ∨ valuation q 83 = false ∨ valuation q 100 = false := by
  rw [value65, value66, value83, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (316 : Vertex) (381 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 65 = true := by
  rw [value65, value67, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(316 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (302 : Vertex) [(316 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 64 = true := by
  rw [value64, value67, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (318 : Vertex) w → w ∈ region → w ≠ (316 : Vertex) → w ∈ [(302 : Vertex)] := by decide
  have hg := other_cover q (318 : Vertex) (316 : Vertex) [(302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 73 = true := by
  rw [value68, value73, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(361 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (355 : Vertex) [(361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 79 = false := by
  rw [value70, value71, value74, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (359 : Vertex) (366 : Vertex) (374 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E159.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112159
