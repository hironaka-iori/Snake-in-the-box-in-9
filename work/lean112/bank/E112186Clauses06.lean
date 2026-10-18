import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 178 = true ∨ valuation q 49 = true ∨ valuation q 55 = true := by
  rw [value49, value54, value55, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(260 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (396 : Vertex) [(260 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 92 = false := by
  rw [value52, value54, value55, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (266 : Vertex) (268 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 94 = false := by
  rw [value56, value57, value60, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value49, value56, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 58 = true := by
  rw [value49, value57, value58, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(260 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(260 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 49 = true ∨ valuation q 56 = true := by
  rw [value49, value56, value57, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value50, value57, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 63 = true := by
  rw [value59, value63, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 58 = true := by
  rw [value58, value59, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 77 = false := by
  rw [value56, value60, value61, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (281 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 56 = false ∨ valuation q 77 = false ∨ valuation q 99 = false := by
  rw [value56, value60, value77, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (344 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 61 = true ∨ valuation q 77 = true ∨ valuation q 99 = true := by
  rw [value60, value61, value77, value99, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(281 : Vertex), (344 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(281 : Vertex), (344 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 56 = true ∨ valuation q 77 = true ∨ valuation q 99 = true := by
  rw [value56, value60, value77, value99, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(272 : Vertex), (344 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (281 : Vertex) [(272 : Vertex), (344 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 56 = true ∨ valuation q 61 = true ∨ valuation q 99 = true := by
  rw [value56, value60, value61, value99, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(272 : Vertex), (281 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (344 : Vertex) [(272 : Vertex), (281 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 56 = true ∨ valuation q 61 = true ∨ valuation q 77 = true := by
  rw [value56, value60, value61, value77, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(272 : Vertex), (281 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (408 : Vertex) [(272 : Vertex), (281 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value51, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 100 = false := by
  rw [value51, value60, value61, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 100 = false := by
  rw [value51, value61, value62, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 100 = false := by
  rw [value60, value61, value62, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 53 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value53, value61, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 61 = true ∨ valuation q 63 = true := by
  rw [value61, value62, value63, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(281 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (267 : Vertex) [(281 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 53 = true ∨ valuation q 63 = true := by
  rw [value53, value62, value63, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(267 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (281 : Vertex) [(267 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 53 = true ∨ valuation q 61 = true := by
  rw [value53, value61, value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(267 : Vertex), (281 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (287 : Vertex) [(267 : Vertex), (281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 81 = false := by
  rw [value59, value62, value63, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (283 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value64, value65, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 105 = false := by
  rw [value64, value65, value66, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 105 = false := by
  rw [value64, value65, value69, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 105 = false := by
  rw [value64, value66, value69, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (322 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value64, value65, value68, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 73 = true := by
  rw [value64, value65, value67, value73, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(320 : Vertex), (323 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (325 : Vertex) [(320 : Vertex), (323 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 68 = true := by
  rw [value64, value65, value67, value68, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(320 : Vertex), (323 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(320 : Vertex), (323 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 47 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value47, value64, value66, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (320 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E186.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112186
