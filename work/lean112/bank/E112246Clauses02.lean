import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 16 = false ∨ valuation q 66 = false ∨ valuation q 75 = false := by
  rw [value16, value66, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (63 : Vertex) (303 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 91 = false := by
  rw [value66, value75, value76, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (303 : Vertex) (318 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value18, value78, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (67 : Vertex) (339 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 93 = false := by
  rw [value18, value78, value81, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (67 : Vertex) (339 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 18 = false ∨ valuation q 82 = false ∨ valuation q 93 = false := by
  rw [value18, value78, value82, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (67 : Vertex) (355 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 93 = false := by
  rw [value78, value81, value82, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (339 : Vertex) (355 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 25 = false ∨ valuation q 85 = false ∨ valuation q 99 = false := by
  rw [value25, value79, value85, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (368 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 99 = false := by
  rw [value79, value80, value85, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (337 : Vertex) (368 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 186 = true ∨ valuation q 79 = true := by
  rw [value79, value80, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (337 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(336 : Vertex)] := by decide
  have hg := other_cover q (337 : Vertex) (339 : Vertex) [(336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 187 = true ∨ valuation q 80 = true := by
  rw [value80, value81, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(337 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (323 : Vertex) [(337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 187 = true ∨ valuation q 78 = true := by
  rw [value78, value81, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (339 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(323 : Vertex)] := by decide
  have hg := other_cover q (339 : Vertex) (337 : Vertex) [(323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 188 = true ∨ valuation q 62 = true ∨ valuation q 84 = true := by
  rw [value62, value82, value84, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(291 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (323 : Vertex) [(291 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 188 = true ∨ valuation q 62 = true ∨ valuation q 78 = true := by
  rw [value62, value78, value82, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(291 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (363 : Vertex) [(291 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 189 = true ∨ valuation q 87 = true := by
  rw [value83, value87, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (293 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (293 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 189 = true ∨ valuation q 63 = true := by
  rw [value63, value83, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(293 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (373 : Vertex) [(293 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 64 = false ∨ valuation q 82 = false ∨ valuation q 90 = false := by
  rw [value64, value82, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (355 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 67 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value67, value79, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (304 : Vertex) (336 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 191 = true ∨ valuation q 67 = true ∨ valuation q 79 = true := by
  rw [value67, value79, value85, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (372 : Vertex) → w ∈ [(304 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (372 : Vertex) [(304 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 192 = true ∨ valuation q 85 = true := by
  rw [value85, value86, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(368 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (373 : Vertex) [(368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value83, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 194 = true ∨ valuation q 91 = true := by
  rw [value88, value91, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 194 = true ∨ valuation q 87 = true := by
  rw [value87, value88, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (383 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 76 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value76, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 198 = true ∨ valuation q 96 = true := by
  rw [value92, value96, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 198 = true ∨ valuation q 93 = true := by
  rw [value92, value93, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(451 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 199 = true ∨ valuation q 92 = true := by
  rw [value92, value93, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(450 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (323 : Vertex) [(450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 199 = true ∨ valuation q 78 = true := by
  rw [value78, value93, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(323 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value94, value95, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (453 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 200 = true ∨ valuation q 97 = true ∨ valuation q 100 = true := by
  rw [value94, value97, value100, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(460 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (453 : Vertex) [(460 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 201 = true ∨ valuation q 101 = true := by
  rw [value95, value101, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 201 = true ∨ valuation q 94 = true := by
  rw [value94, value95, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(452 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (469 : Vertex) [(452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 202 = true ∨ valuation q 98 = true := by
  rw [value96, value98, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (450 : Vertex) [(462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E246.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112246
