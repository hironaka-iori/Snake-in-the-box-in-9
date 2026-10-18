import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 87 = false ∨ valuation q 101 = false := by
  rw [value78, value87, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (426 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 87 = false ∨ valuation q 121 = false := by
  rw [value78, value87, value98, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 97 = false ∨ valuation q 99 = false := by
  rw [value78, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value78, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value78, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 99 = false ∨ valuation q 121 = false := by
  rw [value78, value98, value99, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 78 = false ∨ valuation q 101 = false ∨ valuation q 121 = false := by
  rw [value78, value98, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (410 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 99 = false := by
  rw [value87, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value87, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 97 = false ∨ valuation q 121 = false := by
  rw [value87, value97, value98, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value87, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 99 = false ∨ valuation q 121 = false := by
  rw [value87, value98, value99, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 101 = false ∨ valuation q 121 = false := by
  rw [value87, value98, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value97, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 121 = false := by
  rw [value97, value98, value99, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 121 = false := by
  rw [value97, value98, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (440 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 121 = false := by
  rw [value98, value99, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (443 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value88, value93, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 221 = true ∨ valuation q 93 = true ∨ valuation q 98 = true := by
  rw [value93, value98, value99, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(435 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(435 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 221 = true ∨ valuation q 88 = true ∨ valuation q 98 = true := by
  rw [value88, value98, value99, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (435 : Vertex) [(427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 221 = true ∨ valuation q 88 = true ∨ valuation q 93 = true := by
  rw [value88, value93, value99, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (442 : Vertex) [(427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 39 = false ∨ valuation q 80 = false ∨ valuation q 89 = false := by
  rw [value39, value80, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (317 : Vertex) (413 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 222 = true ∨ valuation q 80 = true ∨ valuation q 89 = true ∨ valuation q 95 = true := by
  rw [value80, value89, value95, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(413 : Vertex), (429 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (317 : Vertex) [(413 : Vertex), (429 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 222 = true ∨ valuation q 39 = true ∨ valuation q 89 = true ∨ valuation q 95 = true := by
  rw [value39, value89, value95, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(317 : Vertex), (429 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (413 : Vertex) [(317 : Vertex), (429 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 222 = true ∨ valuation q 39 = true ∨ valuation q 80 = true ∨ valuation q 89 = true := by
  rw [value39, value80, value89, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(317 : Vertex), (413 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (437 : Vertex) [(317 : Vertex), (413 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value90, value96, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (446 : Vertex) (430 : Vertex) (438 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 40 = true ∨ valuation q 96 = true ∨ valuation q 98 = true := by
  rw [value40, value96, value98, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(318 : Vertex), (438 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (430 : Vertex) [(318 : Vertex), (438 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 224 = true ∨ valuation q 64 = true := by
  rw [value64, value102, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(384 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (320 : Vertex) [(384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 224 = true ∨ valuation q 42 = true := by
  rw [value42, value102, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(320 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (384 : Vertex) [(320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 68 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value68, value103, value104, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (390 : Vertex) (455 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value103, value104, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (455 : Vertex) (470 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 225 = true ∨ valuation q 68 = true ∨ valuation q 107 = true ∨ valuation q 113 = true := by
  rw [value68, value103, value107, value113, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(390 : Vertex), (470 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (455 : Vertex) [(390 : Vertex), (470 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block16 (q : Snake 81) (h : Conditions q) : B112E254.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112254
