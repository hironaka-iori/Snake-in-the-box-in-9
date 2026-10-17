import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 161 = true ∨ valuation q 13 = true ∨ valuation q 39 = true := by
  rw [value13, value35, value39, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (102 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(38 : Vertex), (118 : Vertex)] := by decide
  have hg := other_cover q (102 : Vertex) (70 : Vertex) [(38 : Vertex), (118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 161 = true ∨ valuation q 13 = true ∨ valuation q 33 = true := by
  rw [value13, value33, value35, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (102 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(38 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (102 : Vertex) (118 : Vertex) [(38 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 16 = false ∨ valuation q 37 = false ∨ valuation q 62 = false := by
  rw [value16, value36, value37, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (109 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 162 = true ∨ valuation q 16 = true ∨ valuation q 62 = true := by
  rw [value16, value36, value62, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(41 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (109 : Vertex) [(41 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 163 = true ∨ valuation q 36 = true ∨ valuation q 38 = true := by
  rw [value36, value37, value38, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(105 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (125 : Vertex) [(105 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 164 = true := by
  rw [value38, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (111 : Vertex) (109 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 25 = false ∨ valuation q 35 = false ∨ valuation q 43 = false := by
  rw [value25, value35, value39, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (118 : Vertex) (54 : Vertex) (102 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 165 = true ∨ valuation q 25 = true ∨ valuation q 43 = true := by
  rw [value25, value39, value43, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (102 : Vertex) → w ∈ [(54 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (102 : Vertex) [(54 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 165 = true ∨ valuation q 25 = true ∨ valuation q 35 = true := by
  rw [value25, value35, value39, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(54 : Vertex), (102 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (126 : Vertex) [(54 : Vertex), (102 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 166 = true ∨ valuation q 28 = true := by
  rw [value28, value40, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(58 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (126 : Vertex) [(58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 167 = true ∨ valuation q 43 = true := by
  rw [value41, value43, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 167 = true ∨ valuation q 42 = true := by
  rw [value41, value42, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 168 = true ∨ valuation q 41 = true := by
  rw [value41, value42, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(124 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (109 : Vertex) [(124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 168 = true ∨ valuation q 37 = true := by
  rw [value37, value42, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (124 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 30 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value30, value39, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (62 : Vertex) (118 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value39, value40, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (118 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 169 = true ∨ valuation q 30 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value30, value40, value41, value43, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(62 : Vertex), (122 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (118 : Vertex) [(62 : Vertex), (122 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 169 = true ∨ valuation q 30 = true ∨ valuation q 39 = true ∨ valuation q 40 = true := by
  rw [value30, value39, value40, value43, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(62 : Vertex), (118 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (124 : Vertex) [(62 : Vertex), (118 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 8 = false ∨ valuation q 52 = false ∨ valuation q 87 = false := by
  rw [value8, value44, value52, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (32 : Vertex) (176 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 170 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 87 = true := by
  rw [value44, value45, value48, value52, value87, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (32 : Vertex) → w ∈ [(161 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (32 : Vertex) [(161 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 170 = true ∨ valuation q 8 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 87 = true := by
  rw [value8, value44, value48, value52, value87, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(32 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(32 : Vertex), (168 : Vertex), (176 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 170 = true ∨ valuation q 8 = true ∨ valuation q 45 = true ∨ valuation q 52 = true ∨ valuation q 87 = true := by
  rw [value8, value44, value45, value52, value87, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(32 : Vertex), (161 : Vertex), (176 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (168 : Vertex) [(32 : Vertex), (161 : Vertex), (176 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 170 = true ∨ valuation q 8 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 87 = true := by
  rw [value8, value44, value45, value48, value87, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(32 : Vertex), (161 : Vertex), (168 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (176 : Vertex) [(32 : Vertex), (161 : Vertex), (168 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 170 = true ∨ valuation q 8 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value8, value44, value45, value48, value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(32 : Vertex), (161 : Vertex), (168 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (416 : Vertex) [(32 : Vertex), (161 : Vertex), (168 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 9 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value9, value44, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (160 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 9 = false ∨ valuation q 44 = false ∨ valuation q 53 = false := by
  rw [value9, value44, value45, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (160 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 9 = false ∨ valuation q 46 = false ∨ valuation q 53 = false := by
  rw [value9, value45, value46, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 9 = false ∨ valuation q 46 = false ∨ valuation q 88 = false := by
  rw [value9, value45, value46, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (165 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 9 = false ∨ valuation q 53 = false ∨ valuation q 88 = false := by
  rw [value9, value45, value53, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (177 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 53 = false := by
  rw [value44, value45, value46, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 88 = false := by
  rw [value44, value45, value46, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 53 = false ∨ valuation q 88 = false := by
  rw [value44, value45, value53, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (177 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E121.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112121
