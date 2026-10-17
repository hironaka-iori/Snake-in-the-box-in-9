import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 73 = false ∨ valuation q 85 = false ∨ valuation q 117 = false := by
  rw [value73, value85, value86, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (335 : Vertex) (350 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 79 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value79, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (343 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 79 = false ∨ valuation q 84 = false ∨ valuation q 117 = false := by
  rw [value79, value84, value86, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (343 : Vertex) (349 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 117 = false := by
  rw [value84, value85, value86, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (351 : Vertex) (349 : Vertex) (350 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 205 = true ∨ valuation q 90 = true := by
  rw [value88, value90, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(422 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (421 : Vertex) [(422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 205 = true ∨ valuation q 89 = true := by
  rw [value88, value89, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(421 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (422 : Vertex) [(421 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 95 = true := by
  rw [value89, value95, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (420 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 88 = true := by
  rw [value88, value89, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(420 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 88 = true ∨ valuation q 94 = true := by
  rw [value88, value90, value94, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(420 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (418 : Vertex) [(420 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 87 = true ∨ valuation q 88 = true := by
  rw [value87, value88, value90, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(418 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (430 : Vertex) [(418 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 208 = true ∨ valuation q 93 = true := by
  rw [value91, value93, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(427 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (441 : Vertex) [(427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 87 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value87, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 210 = true ∨ valuation q 92 = true := by
  rw [value92, value93, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(426 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (425 : Vertex) [(426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value90, value92, value94, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 96 = true := by
  rw [value95, value96, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (421 : Vertex) [(439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 212 = true ∨ valuation q 89 = true := by
  rw [value89, value95, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(421 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(421 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 100 = true := by
  rw [value96, value100, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 213 = true ∨ valuation q 95 = true := by
  rw [value95, value96, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = true := by
  rw [value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ∈ [(441 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (440 : Vertex) [(441 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 97 = true := by
  rw [value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 215 = true ∨ valuation q 91 = true := by
  rw [value91, value98, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(425 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (440 : Vertex) [(425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 216 = true ∨ valuation q 28 = true ∨ valuation q 100 = true := by
  rw [value28, value99, value100, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(190 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (430 : Vertex) [(190 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 216 = true ∨ valuation q 28 = true ∨ valuation q 94 = true := by
  rw [value28, value94, value99, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(190 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (447 : Vertex) [(190 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 217 = true ∨ valuation q 99 = true := by
  rw [value99, value100, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(446 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (439 : Vertex) [(446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 217 = true ∨ valuation q 96 = true := by
  rw [value96, value100, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(439 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (446 : Vertex) [(439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 30 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value30, value101, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (194 : Vertex) (454 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value66, value101, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (322 : Vertex) (454 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 102 = true := by
  rw [value102, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (452 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = true ∨ valuation q 104 = true := by
  rw [value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ∈ [(453 : Vertex), (454 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (452 : Vertex) [(453 : Vertex), (454 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 219 = true ∨ valuation q 104 = true := by
  rw [value102, value104, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(454 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (453 : Vertex) [(454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 219 = true ∨ valuation q 103 = true := by
  rw [value102, value103, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(453 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (454 : Vertex) [(453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 220 = true ∨ valuation q 102 = true ∨ valuation q 112 = true := by
  rw [value102, value103, value112, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (197 : Vertex) [(452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block17 (q : Snake 81) (h : Conditions q) : B112E064.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112064
