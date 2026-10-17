import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 220 = true ∨ valuation q 32 = true ∨ valuation q 112 = true := by
  rw [value32, value103, value112, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(197 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(197 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 220 = true ∨ valuation q 32 = true ∨ valuation q 102 = true := by
  rw [value32, value102, value103, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(197 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (469 : Vertex) [(197 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value101, value102, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (450 : Vertex) (452 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 221 = true ∨ valuation q 102 = true ∨ valuation q 108 = true := by
  rw [value102, value104, value108, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (450 : Vertex) [(452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 221 = true ∨ valuation q 101 = true ∨ valuation q 108 = true := by
  rw [value101, value104, value108, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(450 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (452 : Vertex) [(450 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 221 = true ∨ valuation q 101 = true ∨ valuation q 102 = true := by
  rw [value101, value102, value104, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(450 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (462 : Vertex) [(450 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 69 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value69, value105, value107, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (329 : Vertex) (459 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 222 = true ∨ valuation q 107 = true ∨ valuation q 115 = true := by
  rw [value105, value107, value115, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(459 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (329 : Vertex) [(459 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 222 = true ∨ valuation q 69 = true ∨ valuation q 115 = true := by
  rw [value69, value105, value115, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(329 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (459 : Vertex) [(329 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 222 = true ∨ valuation q 69 = true ∨ valuation q 107 = true := by
  rw [value69, value105, value107, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(329 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (473 : Vertex) [(329 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 101 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value101, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (450 : Vertex) (459 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 223 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value106, value107, value108, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(459 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (450 : Vertex) [(459 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 223 = true ∨ valuation q 101 = true ∨ valuation q 108 = true := by
  rw [value101, value106, value108, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(450 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (459 : Vertex) [(450 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 223 = true ∨ valuation q 101 = true ∨ valuation q 107 = true := by
  rw [value101, value106, value107, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (462 : Vertex) [(450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value70, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ∈ [(331 : Vertex), (457 : Vertex), (458 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (459 : Vertex) [(331 : Vertex), (457 : Vertex), (458 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value70, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (331 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value105, value106, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide)

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 224 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value105, value106, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(457 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (331 : Vertex) [(457 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 224 = true ∨ valuation q 70 = true ∨ valuation q 106 = true := by
  rw [value70, value106, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(331 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (457 : Vertex) [(331 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 224 = true ∨ valuation q 70 = true ∨ valuation q 105 = true := by
  rw [value70, value105, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(331 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (458 : Vertex) [(331 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 116 = false := by
  rw [value104, value106, value108, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (454 : Vertex) (458 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 225 = true ∨ valuation q 106 = true ∨ valuation q 116 = true := by
  rw [value106, value108, value116, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(458 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (454 : Vertex) [(458 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 225 = true ∨ valuation q 104 = true ∨ valuation q 116 = true := by
  rw [value104, value108, value116, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(454 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (458 : Vertex) [(454 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 110 = false := by
  rw [value37, value74, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (208 : Vertex) (336 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 37 = false ∨ valuation q 74 = false ∨ valuation q 114 = false := by
  rw [value37, value74, value109, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (208 : Vertex) (336 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 37 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value37, value109, value110, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (208 : Vertex) (465 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 74 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value74, value109, value110, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (336 : Vertex) (465 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 74 = false ∨ valuation q 114 = false := by
  rw [value74, value114, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (464 : Vertex) (336 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 226 = true ∨ valuation q 37 = true ∨ valuation q 74 = true ∨ valuation q 110 = true := by
  rw [value37, value74, value109, value110, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(208 : Vertex), (336 : Vertex), (465 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(208 : Vertex), (336 : Vertex), (465 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 38 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value38, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (209 : Vertex) (464 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 38 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value38, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (209 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 38 = false ∨ valuation q 112 = false ∨ valuation q 115 = false := by
  rw [value38, value110, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (209 : Vertex) (469 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E064.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112064
