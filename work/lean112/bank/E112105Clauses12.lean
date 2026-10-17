import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 63 = true ∨ valuation q 121 = true := by
  rw [value63, value66, value121, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(216 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (204 : Vertex) [(216 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 55 = true ∨ valuation q 121 = true := by
  rw [value55, value66, value121, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(204 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (216 : Vertex) [(204 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 190 = true ∨ valuation q 55 = true ∨ valuation q 63 = true := by
  rw [value55, value63, value66, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(204 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (476 : Vertex) [(204 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 102 = false := by
  rw [value67, value68, value72, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (322 : Vertex) (328 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 191 = true ∨ valuation q 72 = true ∨ valuation q 102 = true := by
  rw [value67, value72, value102, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(328 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (322 : Vertex) [(328 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 191 = true ∨ valuation q 68 = true ∨ valuation q 102 = true := by
  rw [value67, value68, value102, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(322 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(322 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 191 = true ∨ valuation q 68 = true ∨ valuation q 72 = true := by
  rw [value67, value68, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(322 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (448 : Vertex) [(322 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 68 = true := by
  rw [value68, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (322 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 104 = true := by
  rw [value67, value68, value70, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ∈ [(320 : Vertex), (326 : Vertex), (450 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (322 : Vertex) [(320 : Vertex), (326 : Vertex), (450 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 104 = false := by
  rw [value67, value68, value70, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value67, value70, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 67 = false ∨ valuation q 104 = false := by
  rw [value67, value104, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (322 : Vertex) (320 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 70 = false ∨ valuation q 104 = false := by
  rw [value70, value104, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (322 : Vertex) (326 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 70 = true ∨ valuation q 104 = true := by
  rw [value68, value70, value104, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(326 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (320 : Vertex) [(326 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 67 = true ∨ valuation q 104 = true := by
  rw [value67, value68, value104, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(320 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (326 : Vertex) [(320 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 192 = true ∨ valuation q 67 = true ∨ valuation q 70 = true := by
  rw [value67, value68, value70, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(320 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (450 : Vertex) [(320 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 106 = false := by
  rw [value69, value71, value78, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (327 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 71 = true ∨ valuation q 106 = true := by
  rw [value69, value71, value106, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(327 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (341 : Vertex) [(327 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value68, value70, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (327 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 71 = false ∨ valuation q 107 = false := by
  rw [value68, value70, value71, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (327 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 74 = false ∨ valuation q 107 = false := by
  rw [value68, value70, value74, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (334 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 107 = false := by
  rw [value70, value71, value74, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (327 : Vertex) (334 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 71 = true ∨ valuation q 74 = true ∨ valuation q 107 = true := by
  rw [value70, value71, value74, value107, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(327 : Vertex), (334 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (322 : Vertex) [(327 : Vertex), (334 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 68 = true ∨ valuation q 74 = true ∨ valuation q 107 = true := by
  rw [value68, value70, value74, value107, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(322 : Vertex), (334 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(322 : Vertex), (334 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 68 = true ∨ valuation q 71 = true ∨ valuation q 107 = true := by
  rw [value68, value70, value71, value107, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(322 : Vertex), (327 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (334 : Vertex) [(322 : Vertex), (327 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 15 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value15, value71, value75, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (327 : Vertex) (71 : Vertex) (335 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 75 = true ∨ valuation q 79 = true := by
  rw [value69, value70, value71, value75, value79, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(325 : Vertex), (326 : Vertex), (335 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (71 : Vertex) [(325 : Vertex), (326 : Vertex), (335 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 15 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 79 = true := by
  rw [value15, value69, value70, value71, value79, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (335 : Vertex) → w ∈ [(71 : Vertex), (325 : Vertex), (326 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (335 : Vertex) [(71 : Vertex), (325 : Vertex), (326 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 72 = true := by
  rw [value72, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (328 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value67, value72, value73, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ∈ [(320 : Vertex), (329 : Vertex), (344 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (328 : Vertex) [(320 : Vertex), (329 : Vertex), (344 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 67 = false ∨ valuation q 73 = false ∨ valuation q 80 = false := by
  rw [value67, value72, value73, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (320 : Vertex) (329 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value72, value73, value80, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(329 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(329 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block12 (q : Snake 81) (h : Conditions q) : B112E105.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112105
