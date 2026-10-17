import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 52 = true ∨ valuation q 63 = true := by
  rw [value52, value62, value63, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(264 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(264 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 186 = true ∨ valuation q 52 = true ∨ valuation q 57 = true := by
  rw [value52, value57, value62, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(264 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (282 : Vertex) [(264 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value58, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (274 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 187 = true ∨ valuation q 58 = true ∨ valuation q 64 = true := by
  rw [value58, value63, value64, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (280 : Vertex) [(274 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 187 = true ∨ valuation q 58 = true ∨ valuation q 62 = true := by
  rw [value58, value62, value63, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(274 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (283 : Vertex) [(274 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 63 = true := by
  rw [value63, value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(282 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (267 : Vertex) [(282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 188 = true ∨ valuation q 53 = true := by
  rw [value53, value64, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (282 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value65, value66, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (322 : Vertex) (324 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 102 = true := by
  rw [value65, value67, value70, value102, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(324 : Vertex), (328 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (322 : Vertex) [(324 : Vertex), (328 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 66 = true ∨ valuation q 70 = true ∨ valuation q 102 = true := by
  rw [value65, value66, value70, value102, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(322 : Vertex), (328 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (324 : Vertex) [(322 : Vertex), (328 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 102 = true := by
  rw [value65, value66, value67, value102, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(322 : Vertex), (324 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(322 : Vertex), (324 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 189 = true ∨ valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 70 = true := by
  rw [value65, value66, value67, value70, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(322 : Vertex), (324 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (448 : Vertex) [(322 : Vertex), (324 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 75 = false := by
  rw [value65, value66, value68, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 68 = true ∨ valuation q 75 = true := by
  rw [value66, value68, value75, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(326 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (320 : Vertex) [(326 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value65, value66, value68, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(320 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (338 : Vertex) [(320 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 105 = false := by
  rw [value65, value67, value68, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (320 : Vertex) (326 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 191 = true ∨ valuation q 68 = true ∨ valuation q 105 = true := by
  rw [value67, value68, value105, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(326 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (320 : Vertex) [(326 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 191 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value65, value67, value68, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(320 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (452 : Vertex) [(320 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 50 = false ∨ valuation q 66 = false ∨ valuation q 72 = false := by
  rw [value50, value66, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (322 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 50 = false ∨ valuation q 67 = false ∨ valuation q 72 = false := by
  rw [value50, value67, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (324 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value67, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (324 : Vertex) (327 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 51 = false ∨ valuation q 68 = false ∨ valuation q 73 = false := by
  rw [value51, value68, value69, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (263 : Vertex) (326 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 51 = false ∨ valuation q 73 = false ∨ valuation q 107 = false := by
  rw [value51, value69, value73, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (263 : Vertex) (335 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 73 = false ∨ valuation q 107 = false := by
  rw [value68, value69, value73, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (326 : Vertex) (335 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 51 = true ∨ valuation q 68 = true ∨ valuation q 107 = true := by
  rw [value51, value68, value69, value107, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(263 : Vertex), (326 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(263 : Vertex), (326 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value52, value65, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (264 : Vertex) (320 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 108 = false := by
  rw [value52, value65, value70, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (264 : Vertex) (320 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 71 = false ∨ valuation q 108 = false := by
  rw [value52, value70, value71, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (264 : Vertex) (329 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 71 = false ∨ valuation q 108 = false := by
  rw [value65, value70, value71, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (320 : Vertex) (329 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 65 = true ∨ valuation q 71 = true ∨ valuation q 108 = true := by
  rw [value65, value70, value71, value108, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (264 : Vertex) [(320 : Vertex), (329 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 109 = false := by
  rw [value70, value71, value78, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (328 : Vertex) (345 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 78 = true ∨ valuation q 109 = true := by
  rw [value71, value78, value109, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (329 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(345 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (329 : Vertex) (328 : Vertex) [(345 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E153.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112153
