import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 117 = false := by
  rw [value102, value105, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value102, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value105, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value105, value106, value107, value117, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(457 : Vertex), (458 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (451 : Vertex) [(457 : Vertex), (458 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 225 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 117 = true := by
  rw [value102, value105, value107, value117, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(451 : Vertex), (457 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (458 : Vertex) [(451 : Vertex), (457 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = true ∨ valuation q 103 = true ∨ valuation q 109 = true := by
  rw [value88, value103, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ∈ [(396 : Vertex), (452 : Vertex), (462 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (460 : Vertex) [(396 : Vertex), (452 : Vertex), (462 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value88, value103, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (396 : Vertex) (452 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 103 = true ∨ valuation q 109 = true := by
  rw [value103, value108, value109, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (396 : Vertex) [(452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value88, value108, value109, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(396 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (452 : Vertex) [(396 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 103 = true := by
  rw [value88, value103, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(396 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (462 : Vertex) [(396 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 90 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value90, value106, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 90 = true ∨ valuation q 108 = true := by
  rw [value90, value108, value109, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(398 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (458 : Vertex) [(398 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 90 = true ∨ valuation q 106 = true := by
  rw [value90, value106, value109, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(398 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (460 : Vertex) [(398 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 92 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value92, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (400 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 228 = true ∨ valuation q 92 = true ∨ valuation q 115 = true := by
  rw [value92, value110, value115, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(400 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (468 : Vertex) [(400 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 228 = true ∨ valuation q 92 = true ∨ valuation q 111 = true := by
  rw [value92, value110, value111, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(400 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(400 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 103 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value103, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 103 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value103, value110, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 103 = true ∨ valuation q 112 = true ∨ valuation q 113 = true := by
  rw [value103, value111, value112, value113, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(452 : Vertex), (469 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (464 : Vertex) [(452 : Vertex), (469 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 103 = true ∨ valuation q 110 = true ∨ valuation q 112 = true := by
  rw [value103, value110, value111, value112, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(452 : Vertex), (464 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (470 : Vertex) [(452 : Vertex), (464 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 104 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value104, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 46 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value46, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 96 = false ∨ valuation q 111 = false := by
  rw [value75, value96, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (342 : Vertex) (406 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 96 = false ∨ valuation q 114 = false := by
  rw [value75, value96, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (342 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 75 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value75, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (342 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 96 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value96, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (406 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 232 = true ∨ valuation q 113 = true ∨ valuation q 118 = true := by
  rw [value113, value114, value118, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(470 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (469 : Vertex) [(470 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 232 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value112, value114, value118, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(469 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (470 : Vertex) [(469 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 232 = true ∨ valuation q 112 = true ∨ valuation q 113 = true := by
  rw [value112, value113, value114, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(469 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (479 : Vertex) [(469 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 115 = true := by
  rw [value115, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (472 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 110 = true ∨ valuation q 116 = true := by
  rw [value110, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ∈ [(464 : Vertex), (473 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (472 : Vertex) [(464 : Vertex), (473 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 116 = true := by
  rw [value115, value116, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(473 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block18 (q : Snake 81) (h : Conditions q) : B112E027.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112027
