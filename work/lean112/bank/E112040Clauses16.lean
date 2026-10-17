import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 85 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value85, value89, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (307 : Vertex) (379 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 109 = false ∨ valuation q 116 = false := by
  rw [value88, value89, value109, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (314 : Vertex) (379 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 209 = true ∨ valuation q 85 = true ∨ valuation q 109 = true ∨ valuation q 116 = true := by
  rw [value85, value89, value109, value116, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(307 : Vertex), (379 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (314 : Vertex) [(307 : Vertex), (379 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 210 = true ∨ valuation q 81 = true ∨ valuation q 91 = true := by
  rw [value81, value90, value91, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (316 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(300 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (316 : Vertex) (308 : Vertex) [(300 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 82 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value82, value90, value91, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (317 : Vertex) (301 : Vertex) (316 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 75 = false ∨ valuation q 93 = false := by
  rw [value20, value75, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (96 : Vertex) (288 : Vertex) (356 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 75 = false ∨ valuation q 97 = false := by
  rw [value20, value75, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (96 : Vertex) (288 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 93 = false ∨ valuation q 102 = false := by
  rw [value20, value92, value93, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (96 : Vertex) (356 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 75 = false ∨ valuation q 93 = false ∨ valuation q 102 = false := by
  rw [value75, value92, value93, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (352 : Vertex) (288 : Vertex) (356 : Vertex) (368 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 212 = true ∨ valuation q 20 = true ∨ valuation q 75 = true ∨ valuation q 97 = true ∨ valuation q 102 = true := by
  rw [value20, value75, value92, value97, value102, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (352 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(96 : Vertex), (288 : Vertex), (360 : Vertex), (368 : Vertex)] := by decide
  have hg := other_cover q (352 : Vertex) (356 : Vertex) [(96 : Vertex), (288 : Vertex), (360 : Vertex), (368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value92, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (352 : Vertex) (357 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 213 = true ∨ valuation q 92 = true ∨ valuation q 94 = true := by
  rw [value92, value93, value94, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (358 : Vertex) → w ∈ [(352 : Vertex), (357 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (358 : Vertex) [(352 : Vertex), (357 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 214 = true ∨ valuation q 96 = true ∨ valuation q 104 = true := by
  rw [value94, value96, value104, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(359 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (356 : Vertex) [(359 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 214 = true ∨ valuation q 93 = true ∨ valuation q 104 = true := by
  rw [value93, value94, value104, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(356 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (359 : Vertex) [(356 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 214 = true ∨ valuation q 93 = true ∨ valuation q 96 = true := by
  rw [value93, value94, value96, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(356 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (373 : Vertex) [(356 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 101 = false := by
  rw [value93, value95, value96, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (358 : Vertex) (356 : Vertex) (359 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 215 = true ∨ valuation q 96 = true ∨ valuation q 101 = true := by
  rw [value95, value96, value101, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(359 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (356 : Vertex) [(359 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 215 = true ∨ valuation q 93 = true ∨ valuation q 96 = true := by
  rw [value93, value95, value96, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(356 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (366 : Vertex) [(356 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 24 = false ∨ valuation q 79 = false ∨ valuation q 94 = false := by
  rw [value24, value79, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (295 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 24 = false ∨ valuation q 79 = false ∨ valuation q 95 = false := by
  rw [value24, value79, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (295 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 24 = false ∨ valuation q 79 = false ∨ valuation q 105 = false := by
  rw [value24, value79, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (295 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 24 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value24, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (357 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 24 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value24, value94, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (357 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 24 = false ∨ valuation q 95 = false ∨ valuation q 105 = false := by
  rw [value24, value95, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (103 : Vertex) (358 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 79 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value79, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (357 : Vertex) (358 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 79 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value79, value94, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (357 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 79 = false ∨ valuation q 95 = false ∨ valuation q 105 = false := by
  rw [value79, value95, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (358 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 105 = false := by
  rw [value94, value95, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (357 : Vertex) (358 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 98 = false := by
  rw [value80, value92, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value80, value92, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 80 = false ∨ valuation q 92 = false ∨ valuation q 106 = false := by
  rw [value80, value92, value97, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (352 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 80 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value80, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (361 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E040.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112040
