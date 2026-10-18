import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 101 = false := by
  rw [value89, value91, value93, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (423 : Vertex) (427 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 101 = true := by
  rw [value88, value89, value91, value93, value101, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(418 : Vertex), (423 : Vertex), (427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (417 : Vertex) [(418 : Vertex), (423 : Vertex), (427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 93 = true ∨ valuation q 101 = true := by
  rw [value87, value89, value91, value93, value101, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex), (427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (418 : Vertex) [(417 : Vertex), (423 : Vertex), (427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 93 = true ∨ valuation q 101 = true := by
  rw [value87, value88, value89, value93, value101, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(417 : Vertex), (418 : Vertex), (427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (423 : Vertex) [(417 : Vertex), (418 : Vertex), (427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 101 = true := by
  rw [value87, value88, value89, value91, value101, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(417 : Vertex), (418 : Vertex), (423 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (427 : Vertex) [(417 : Vertex), (418 : Vertex), (423 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 93 = true := by
  rw [value87, value88, value89, value91, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(417 : Vertex), (418 : Vertex), (423 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (435 : Vertex) [(417 : Vertex), (418 : Vertex), (423 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 36 = false ∨ valuation q 87 = false ∨ valuation q 95 = false := by
  rw [value36, value87, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (417 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 36 = false ∨ valuation q 91 = false ∨ valuation q 95 = false := by
  rw [value36, value90, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (165 : Vertex) (423 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 95 = false := by
  rw [value87, value90, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (423 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value87, value90, value91, value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (165 : Vertex) [(417 : Vertex), (423 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 36 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value36, value90, value91, value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(165 : Vertex), (423 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (417 : Vertex) [(165 : Vertex), (423 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 36 = true ∨ valuation q 87 = true ∨ valuation q 95 = true := by
  rw [value36, value87, value90, value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(165 : Vertex), (417 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (423 : Vertex) [(165 : Vertex), (417 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 36 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value36, value87, value90, value91, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(165 : Vertex), (417 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (429 : Vertex) [(165 : Vertex), (417 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 73 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value73, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (419 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 73 = false ∨ valuation q 89 = false ∨ valuation q 97 = false := by
  rw [value73, value89, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (419 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 73 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value73, value89, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (419 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 73 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value73, value90, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 73 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value73, value90, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 73 = false ∨ valuation q 97 = false ∨ valuation q 112 = false := by
  rw [value73, value91, value97, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value89, value90, value91, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (421 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value89, value90, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (421 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 112 = false := by
  rw [value89, value91, value97, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 112 = false := by
  rw [value90, value91, value97, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 74 = false ∨ valuation q 86 = false := by
  rw [value38, value74, value86, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 74 = false ∨ valuation q 94 = false := by
  rw [value38, value74, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 74 = false ∨ valuation q 103 = false := by
  rw [value38, value74, value92, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 74 = false ∨ valuation q 113 = false := by
  rw [value38, value74, value92, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 86 = false ∨ valuation q 94 = false := by
  rw [value38, value86, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 86 = false ∨ valuation q 103 = false := by
  rw [value38, value86, value92, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 86 = false ∨ valuation q 113 = false := by
  rw [value38, value86, value92, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (416 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 94 = false ∨ valuation q 103 = false := by
  rw [value38, value92, value94, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 38 = false ∨ valuation q 103 = false ∨ valuation q 113 = false := by
  rw [value38, value92, value103, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E008.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112008
