import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 217 = true ∨ valuation q 92 = true ∨ valuation q 97 = true := by
  rw [value92, value97, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (410 : Vertex) [(403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 97 = true := by
  rw [value97, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(409 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (405 : Vertex) [(409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 218 = true ∨ valuation q 93 = true := by
  rw [value93, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(405 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (409 : Vertex) [(405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 65 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value65, value81, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 65 = false ∨ valuation q 81 = false ∨ valuation q 106 = false := by
  rw [value65, value81, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (386 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 65 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value65, value101, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 81 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value81, value101, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 65 = true ∨ valuation q 102 = true ∨ valuation q 106 = true := by
  rw [value65, value101, value102, value106, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(322 : Vertex), (451 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (386 : Vertex) [(322 : Vertex), (451 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 65 = true ∨ valuation q 81 = true ∨ valuation q 106 = true := by
  rw [value65, value81, value101, value106, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(322 : Vertex), (386 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(322 : Vertex), (386 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 219 = true ∨ valuation q 65 = true ∨ valuation q 81 = true ∨ valuation q 102 = true := by
  rw [value65, value81, value101, value102, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(322 : Vertex), (386 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(322 : Vertex), (386 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 82 = false ∨ valuation q 101 = false ∨ valuation q 112 = false := by
  rw [value82, value101, value102, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (387 : Vertex) (450 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 82 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value82, value102, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (387 : Vertex) (459 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 101 = true ∨ valuation q 107 = true ∨ valuation q 112 = true := by
  rw [value101, value102, value107, value112, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(450 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (387 : Vertex) [(450 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 82 = true ∨ valuation q 107 = true ∨ valuation q 112 = true := by
  rw [value82, value102, value107, value112, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(387 : Vertex), (459 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(387 : Vertex), (459 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 82 = true ∨ valuation q 101 = true ∨ valuation q 112 = true := by
  rw [value82, value101, value102, value112, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(387 : Vertex), (450 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(387 : Vertex), (450 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 220 = true ∨ valuation q 82 = true ∨ valuation q 101 = true ∨ valuation q 107 = true := by
  rw [value82, value101, value102, value107, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(387 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(387 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 83 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value83, value103, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (453 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 103 = true ∨ valuation q 108 = true := by
  rw [value103, value104, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ∈ [(452 : Vertex), (461 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (453 : Vertex) [(452 : Vertex), (461 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 108 = true := by
  rw [value104, value108, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(461 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 222 = true ∨ valuation q 103 = true := by
  rw [value103, value104, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(452 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (461 : Vertex) [(452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 38 = true ∨ valuation q 87 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value38, value87, value105, value107, value108, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(201 : Vertex), (393 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (329 : Vertex) [(201 : Vertex), (393 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 223 = true ∨ valuation q 38 = true ∨ valuation q 69 = true ∨ valuation q 107 = true ∨ valuation q 108 = true := by
  rw [value38, value69, value105, value107, value108, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (393 : Vertex) [(201 : Vertex), (329 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 70 = true ∨ valuation q 88 = true ∨ valuation q 101 = true ∨ valuation q 107 = true := by
  rw [value70, value88, value101, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ∈ [(330 : Vertex), (394 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (458 : Vertex) [(330 : Vertex), (394 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 70 = false ∨ valuation q 88 = false ∨ valuation q 107 = false := by
  rw [value70, value88, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (330 : Vertex) (394 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 224 = true ∨ valuation q 88 = true ∨ valuation q 101 = true ∨ valuation q 107 = true := by
  rw [value88, value101, value106, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(394 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (330 : Vertex) [(394 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 224 = true ∨ valuation q 70 = true ∨ valuation q 101 = true ∨ valuation q 107 = true := by
  rw [value70, value101, value106, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(330 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (394 : Vertex) [(330 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 224 = true ∨ valuation q 70 = true ∨ valuation q 88 = true ∨ valuation q 107 = true := by
  rw [value70, value88, value106, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(330 : Vertex), (394 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (450 : Vertex) [(330 : Vertex), (394 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 224 = true ∨ valuation q 70 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value70, value88, value101, value106, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(330 : Vertex), (394 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (459 : Vertex) [(330 : Vertex), (394 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value102, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value102, value105, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value102, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (458 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value105, value106, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E007.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112007
