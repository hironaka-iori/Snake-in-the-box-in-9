import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = true ∨ valuation q 70 = true ∨ valuation q 95 = true := by
  rw [value62, value63, value70, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ∈ [(356 : Vertex), (373 : Vertex), (485 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (357 : Vertex) [(356 : Vertex), (373 : Vertex), (485 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 173 = true ∨ valuation q 60 = true ∨ valuation q 65 = true := by
  rw [value60, value64, value65, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(354 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (366 : Vertex) [(354 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 74 = false := by
  rw [value61, value64, value65, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 61 = false ∨ valuation q 74 = false ∨ valuation q 98 = false := by
  rw [value61, value65, value74, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (379 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 74 = false ∨ valuation q 98 = false := by
  rw [value64, value65, value74, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (362 : Vertex) (379 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 175 = true ∨ valuation q 62 = true := by
  rw [value62, value66, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (366 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value57, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (372 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 69 = false ∨ valuation q 101 = false := by
  rw [value57, value68, value69, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (372 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 57 = false ∨ valuation q 72 = false ∨ valuation q 101 = false := by
  rw [value57, value68, value72, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (376 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 101 = false := by
  rw [value68, value69, value72, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (372 : Vertex) (376 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 70 = true := by
  rw [value62, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ∈ [(356 : Vertex), (368 : Vertex), (373 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (372 : Vertex) [(356 : Vertex), (368 : Vertex), (373 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 62 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value62, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (356 : Vertex) (368 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 178 = true ∨ valuation q 68 = true ∨ valuation q 70 = true := by
  rw [value68, value69, value70, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(368 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (356 : Vertex) [(368 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 178 = true ∨ valuation q 62 = true ∨ valuation q 70 = true := by
  rw [value62, value69, value70, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(356 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (368 : Vertex) [(356 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 63 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value63, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 179 = true ∨ valuation q 63 = true ∨ valuation q 71 = true := by
  rw [value63, value70, value71, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(357 : Vertex), (375 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (372 : Vertex) [(357 : Vertex), (375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 75 = true := by
  rw [value71, value75, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (383 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 181 = true ∨ valuation q 73 = true := by
  rw [value72, value73, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(377 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (368 : Vertex) [(377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 181 = true ∨ valuation q 68 = true := by
  rw [value68, value72, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (377 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 182 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (379 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 65 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value65, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (377 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 183 = true ∨ valuation q 73 = true ∨ valuation q 75 = true := by
  rw [value73, value74, value75, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(377 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (363 : Vertex) [(377 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 183 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value65, value73, value74, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(363 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (383 : Vertex) [(363 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 184 = true ∨ valuation q 74 = true := by
  rw [value74, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(379 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (375 : Vertex) [(379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 184 = true ∨ valuation q 71 = true := by
  rw [value71, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(375 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (379 : Vertex) [(375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 15 = false ∨ valuation q 77 = false ∨ valuation q 80 = false := by
  rw [value15, value76, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (162 : Vertex) (419 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 16 = false ∨ valuation q 56 = false ∨ valuation q 76 = false := by
  rw [value16, value56, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (163 : Vertex) (291 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value78, value79, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 17 = false ∨ valuation q 78 = false ∨ valuation q 86 = false := by
  rw [value17, value78, value79, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 188 = true ∨ valuation q 17 = true ∨ valuation q 78 = true ∨ valuation q 95 = true := by
  rw [value17, value78, value79, value95, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(165 : Vertex), (420 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(165 : Vertex), (420 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 189 = true ∨ valuation q 76 = true ∨ valuation q 81 = true ∨ valuation q 90 = true := by
  rw [value76, value80, value81, value90, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(418 : Vertex), (427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(418 : Vertex), (427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E205.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112205
