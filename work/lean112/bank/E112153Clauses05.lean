import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 179 = true ∨ valuation q 49 = true ∨ valuation q 54 = true ∨ valuation q 56 = true := by
  rw [value49, value54, value55, value56, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (269 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(261 : Vertex), (268 : Vertex), (271 : Vertex)] := by decide
  have hg := other_cover q (269 : Vertex) (397 : Vertex) [(261 : Vertex), (268 : Vertex), (271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value51, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (267 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value51, value55, value56, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (263 : Vertex) (269 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 73 = false := by
  rw [value53, value55, value56, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (269 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 91 = false := by
  rw [value53, value55, value56, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (269 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value53, value56, value73, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 73 = false ∨ valuation q 91 = false := by
  rw [value55, value56, value73, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (269 : Vertex) (335 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 62 = false := by
  rw [value57, value58, value59, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (276 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 92 = false := by
  rw [value57, value58, value62, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (274 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 92 = false := by
  rw [value57, value59, value62, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 59 = true ∨ valuation q 62 = true ∨ valuation q 92 = true := by
  rw [value57, value59, value62, value92, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(276 : Vertex), (280 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (274 : Vertex) [(276 : Vertex), (280 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 181 = true ∨ valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 92 = true := by
  rw [value57, value58, value59, value92, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(274 : Vertex), (276 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value57, value58, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (272 : Vertex) (278 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 75 = false := by
  rw [value57, value58, value61, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (272 : Vertex) (278 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 94 = false := by
  rw [value57, value58, value61, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (272 : Vertex) (278 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 63 = false ∨ valuation q 75 = false := by
  rw [value57, value58, value63, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (272 : Vertex) (282 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 63 = false ∨ valuation q 94 = false := by
  rw [value57, value58, value63, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (272 : Vertex) (282 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 75 = false := by
  rw [value58, value61, value63, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (278 : Vertex) (282 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 94 = false := by
  rw [value58, value61, value63, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (278 : Vertex) (282 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 75 = false ∨ valuation q 94 = false := by
  rw [value58, value61, value75, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (278 : Vertex) (338 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 63 = false ∨ valuation q 75 = false ∨ valuation q 94 = false := by
  rw [value58, value63, value75, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (282 : Vertex) (338 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value57, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (272 : Vertex) (277 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 57 = true ∨ valuation q 61 = true := by
  rw [value57, value59, value61, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(272 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(272 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 49 = false ∨ valuation q 59 = false ∨ valuation q 77 = false := by
  rw [value49, value59, value60, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 59 = true ∨ valuation q 77 = true := by
  rw [value59, value60, value77, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(276 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (261 : Vertex) [(276 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 49 = true ∨ valuation q 77 = true := by
  rw [value49, value60, value77, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (341 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (276 : Vertex) [(261 : Vertex), (341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 184 = true ∨ valuation q 49 = true ∨ valuation q 59 = true := by
  rw [value49, value59, value60, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(261 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (341 : Vertex) [(261 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 58 = true ∨ valuation q 59 = true := by
  rw [value58, value59, value61, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (262 : Vertex) [(274 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 50 = true ∨ valuation q 59 = true := by
  rw [value50, value59, value61, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(262 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (274 : Vertex) [(262 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 185 = true ∨ valuation q 50 = true ∨ valuation q 58 = true := by
  rw [value50, value58, value61, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(262 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (276 : Vertex) [(262 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 52 = false ∨ valuation q 57 = false ∨ valuation q 63 = false := by
  rw [value52, value57, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (272 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 57 = true ∨ valuation q 63 = true := by
  rw [value57, value62, value63, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(272 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (264 : Vertex) [(272 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E153.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112153
