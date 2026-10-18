import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 68 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 116 = true := by
  rw [value68, value85, value102, value104, value105, value107, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(322 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (194 : Vertex) [(322 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 48 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 116 = true := by
  rw [value48, value85, value102, value104, value105, value107, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(194 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (322 : Vertex) [(194 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 116 = true := by
  rw [value48, value68, value102, value104, value105, value107, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(194 : Vertex), (322 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (386 : Vertex) [(194 : Vertex), (322 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 85 = true ∨ valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 116 = true := by
  rw [value48, value68, value85, value104, value105, value107, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(194 : Vertex), (322 : Vertex), (386 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (448 : Vertex) [(194 : Vertex), (322 : Vertex), (386 : Vertex), (451 : Vertex), (454 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 107 = true ∨ valuation q 116 = true := by
  rw [value48, value68, value85, value102, value104, value107, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(194 : Vertex), (322 : Vertex), (386 : Vertex), (448 : Vertex), (454 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(194 : Vertex), (322 : Vertex), (386 : Vertex), (448 : Vertex), (454 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 116 = true := by
  rw [value48, value68, value85, value102, value104, value105, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(194 : Vertex), (322 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (454 : Vertex) [(194 : Vertex), (322 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 228 = true ∨ valuation q 48 = true ∨ valuation q 68 = true ∨ valuation q 85 = true ∨ valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 107 = true := by
  rw [value48, value68, value85, value102, value104, value105, value107, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(194 : Vertex), (322 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (466 : Vertex) [(194 : Vertex), (322 : Vertex), (386 : Vertex), (448 : Vertex), (451 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 105 = true := by
  rw [value105, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (451 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value103, value104, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ∈ [(449 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (451 : Vertex) [(449 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 229 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value104, value105, value109, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (449 : Vertex) [(450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 229 = true ∨ valuation q 103 = true ∨ valuation q 109 = true := by
  rw [value103, value105, value109, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(449 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(449 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 229 = true ∨ valuation q 103 = true ∨ valuation q 104 = true := by
  rw [value103, value104, value105, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(449 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(449 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 50 = false ∨ valuation q 69 = false ∨ valuation q 103 = false := by
  rw [value50, value69, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (197 : Vertex) (325 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 50 = false ∨ valuation q 86 = false ∨ valuation q 103 = false := by
  rw [value50, value86, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (197 : Vertex) (389 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 50 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value50, value103, value106, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (197 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 69 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value69, value103, value106, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (325 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value86, value103, value106, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (389 : Vertex) (449 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 103 = false ∨ valuation q 111 = false ∨ valuation q 118 = false := by
  rw [value103, value106, value111, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (453 : Vertex) (449 : Vertex) (461 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 69 = true ∨ valuation q 86 = true ∨ valuation q 103 = true ∨ valuation q 111 = true ∨ valuation q 118 = true := by
  rw [value69, value86, value103, value106, value111, value118, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(325 : Vertex), (389 : Vertex), (449 : Vertex), (461 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (197 : Vertex) [(325 : Vertex), (389 : Vertex), (449 : Vertex), (461 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 230 = true ∨ valuation q 50 = true ∨ valuation q 86 = true ∨ valuation q 103 = true ∨ valuation q 111 = true ∨ valuation q 118 = true := by
  rw [value50, value86, value103, value106, value111, value118, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(197 : Vertex), (389 : Vertex), (449 : Vertex), (461 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (325 : Vertex) [(197 : Vertex), (389 : Vertex), (449 : Vertex), (461 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 51 = false ∨ valuation q 70 = false ∨ valuation q 87 = false := by
  rw [value51, value70, value87, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (198 : Vertex) (326 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 51 = false ∨ valuation q 87 = false ∨ valuation q 112 = false := by
  rw [value51, value87, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (198 : Vertex) (390 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 51 = false ∨ valuation q 87 = false ∨ valuation q 119 = false := by
  rw [value51, value87, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (198 : Vertex) (390 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 51 = false ∨ valuation q 104 = false ∨ valuation q 112 = false := by
  rw [value51, value104, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (198 : Vertex) (450 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 87 = false ∨ valuation q 112 = false := by
  rw [value70, value87, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (326 : Vertex) (390 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 87 = false ∨ valuation q 119 = false := by
  rw [value70, value87, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (326 : Vertex) (390 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 70 = false ∨ valuation q 112 = false ∨ valuation q 119 = false := by
  rw [value70, value107, value112, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (326 : Vertex) (462 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 87 = false ∨ valuation q 104 = false ∨ valuation q 119 = false := by
  rw [value87, value104, value107, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (390 : Vertex) (450 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 87 = false ∨ valuation q 112 = false ∨ valuation q 119 = false := by
  rw [value87, value107, value112, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (390 : Vertex) (462 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 104 = false ∨ valuation q 112 = false ∨ valuation q 119 = false := by
  rw [value104, value107, value112, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (450 : Vertex) (462 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 70 = true ∨ valuation q 87 = true ∨ valuation q 104 = true ∨ valuation q 112 = true ∨ valuation q 119 = true := by
  rw [value70, value87, value104, value107, value112, value119, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(326 : Vertex), (390 : Vertex), (450 : Vertex), (462 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (198 : Vertex) [(326 : Vertex), (390 : Vertex), (450 : Vertex), (462 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 231 = true ∨ valuation q 51 = true ∨ valuation q 87 = true ∨ valuation q 104 = true ∨ valuation q 112 = true ∨ valuation q 119 = true := by
  rw [value51, value87, value104, value107, value112, value119, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(198 : Vertex), (390 : Vertex), (450 : Vertex), (462 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (326 : Vertex) [(198 : Vertex), (390 : Vertex), (450 : Vertex), (462 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block20 (q : Snake 81) (h : Conditions q) : B112E105.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112105
