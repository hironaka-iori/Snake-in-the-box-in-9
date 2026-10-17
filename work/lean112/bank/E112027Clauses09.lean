import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 9 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value9, value64, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (65 : Vertex) (329 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 72 = false := by
  rw [value63, value64, value65, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 182 = true ∨ valuation q 9 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 69 = true := by
  rw [value9, value63, value64, value65, value69, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(65 : Vertex), (320 : Vertex), (325 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(65 : Vertex), (320 : Vertex), (325 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 67 = false := by
  rw [value54, value64, value65, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 70 = false := by
  rw [value54, value64, value65, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 54 = false ∨ valuation q 64 = false ∨ valuation q 104 = false := by
  rw [value54, value64, value65, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (321 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 54 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value54, value65, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (327 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 54 = false ∨ valuation q 67 = false ∨ valuation q 104 = false := by
  rw [value54, value65, value67, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 54 = false ∨ valuation q 70 = false ∨ valuation q 104 = false := by
  rw [value54, value65, value70, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (261 : Vertex) (333 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value64, value65, value67, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (321 : Vertex) (327 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 104 = false := by
  rw [value64, value65, value67, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (321 : Vertex) (327 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 70 = false ∨ valuation q 104 = false := by
  rw [value64, value65, value70, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (321 : Vertex) (333 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 104 = false := by
  rw [value65, value67, value70, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (327 : Vertex) (333 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 11 = false ∨ valuation q 55 = false ∨ valuation q 67 = false := by
  rw [value11, value55, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (70 : Vertex) (262 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 11 = false ∨ valuation q 67 = false ∨ valuation q 75 = false := by
  rw [value11, value66, value67, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (70 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 55 = false ∨ valuation q 67 = false ∨ valuation q 75 = false := by
  rw [value55, value66, value67, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (262 : Vertex) (327 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 55 = true ∨ valuation q 67 = true ∨ valuation q 75 = true := by
  rw [value55, value66, value67, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(262 : Vertex), (327 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (70 : Vertex) [(262 : Vertex), (327 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 11 = true ∨ valuation q 55 = true ∨ valuation q 75 = true := by
  rw [value11, value55, value66, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(70 : Vertex), (262 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(70 : Vertex), (262 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 66 = true ∨ valuation q 71 = true := by
  rw [value66, value67, value71, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(326 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (325 : Vertex) [(326 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 65 = true ∨ valuation q 71 = true := by
  rw [value65, value67, value71, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(325 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(325 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 65 = true ∨ valuation q 66 = true := by
  rw [value65, value66, value67, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(325 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 68 = true := by
  rw [value68, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (328 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 63 = true ∨ valuation q 69 = true := by
  rw [value63, value68, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (72 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 12 = true ∨ valuation q 69 = true := by
  rw [value12, value68, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(72 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(72 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 12 = true ∨ valuation q 63 = true := by
  rw [value12, value63, value68, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(72 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (329 : Vertex) [(72 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 64 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value64, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (321 : Vertex) (328 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 105 = false := by
  rw [value68, value69, value70, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (329 : Vertex) (328 : Vertex) (333 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 78 = false := by
  rw [value69, value70, value71, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (329 : Vertex) (335 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 188 = true ∨ valuation q 65 = true ∨ valuation q 69 = true ∨ valuation q 78 = true := by
  rw [value65, value69, value70, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(325 : Vertex), (329 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (335 : Vertex) [(325 : Vertex), (329 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 188 = true ∨ valuation q 65 = true ∨ valuation q 69 = true ∨ valuation q 71 = true := by
  rw [value65, value69, value70, value71, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(325 : Vertex), (329 : Vertex), (335 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(325 : Vertex), (329 : Vertex), (335 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 189 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (327 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 189 = true ∨ valuation q 67 = true := by
  rw [value67, value71, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (335 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (335 : Vertex) (333 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E027.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112027
