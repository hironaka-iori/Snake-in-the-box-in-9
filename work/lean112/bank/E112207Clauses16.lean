import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 15 = true ∨ valuation q 45 = true ∨ valuation q 86 = true ∨ valuation q 95 = true := by
  rw [value15, value45, value85, value86, value95, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (385 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (392 : Vertex) [(128 : Vertex), (256 : Vertex), (385 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 202 = true ∨ valuation q 15 = true ∨ valuation q 45 = true ∨ valuation q 86 = true ∨ valuation q 90 = true := by
  rw [value15, value45, value85, value86, value90, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(128 : Vertex), (256 : Vertex), (385 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [(128 : Vertex), (256 : Vertex), (385 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 46 = true ∨ valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value46, value85, value86, value87, value91, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ∈ [(257 : Vertex), (384 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (385 : Vertex) [(257 : Vertex), (384 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 46 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value46, value86, value87, value91, value96, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(257 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (384 : Vertex) [(257 : Vertex), (389 : Vertex), (393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 46 = true ∨ valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 96 = true := by
  rw [value46, value85, value86, value87, value96, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(257 : Vertex), (384 : Vertex), (389 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (393 : Vertex) [(257 : Vertex), (384 : Vertex), (389 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 203 = true ∨ valuation q 46 = true ∨ valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value46, value85, value86, value87, value91, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (385 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(257 : Vertex), (384 : Vertex), (389 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (385 : Vertex) (401 : Vertex) [(257 : Vertex), (384 : Vertex), (389 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 49 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value49, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 49 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value49, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 49 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value49, value87, value89, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (261 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value86, value87, value89, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (385 : Vertex) (391 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 50 = false ∨ valuation q 89 = false := by
  rw [value18, value50, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (262 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 18 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value18, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (134 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 50 = false ∨ valuation q 89 = false ∨ valuation q 99 = false := by
  rw [value50, value88, value89, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (262 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 51 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 94 = true := by
  rw [value51, value87, value88, value89, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(263 : Vertex), (389 : Vertex), (390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (135 : Vertex) [(263 : Vertex), (389 : Vertex), (390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 19 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 94 = true := by
  rw [value19, value87, value88, value89, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(135 : Vertex), (389 : Vertex), (390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (263 : Vertex) [(135 : Vertex), (389 : Vertex), (390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 206 = true ∨ valuation q 19 = true ∨ valuation q 51 = true ∨ valuation q 88 = true ∨ valuation q 94 = true := by
  rw [value19, value51, value88, value89, value94, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(135 : Vertex), (263 : Vertex), (390 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (389 : Vertex) [(135 : Vertex), (263 : Vertex), (390 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 90 = true := by
  rw [value90, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (392 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = true ∨ valuation q 52 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value20, value52, value85, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ∈ [(136 : Vertex), (264 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (392 : Vertex) [(136 : Vertex), (264 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value20, value52, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (136 : Vertex) (264 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 52 = false ∨ valuation q 91 = false := by
  rw [value20, value52, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (136 : Vertex) (264 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 85 = false ∨ valuation q 91 = false := by
  rw [value20, value85, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (136 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 91 = false := by
  rw [value52, value85, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (392 : Vertex) (264 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 20 = false ∨ valuation q 91 = false := by
  rw [value20, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (392 : Vertex) (136 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 85 = false ∨ valuation q 91 = false := by
  rw [value85, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (392 : Vertex) (384 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 52 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value52, value85, value90, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(264 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (136 : Vertex) [(264 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 20 = true ∨ valuation q 85 = true ∨ valuation q 91 = true := by
  rw [value20, value85, value90, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(136 : Vertex), (384 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (264 : Vertex) [(136 : Vertex), (384 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 20 = true ∨ valuation q 52 = true ∨ valuation q 91 = true := by
  rw [value20, value52, value90, value91, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(136 : Vertex), (264 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (384 : Vertex) [(136 : Vertex), (264 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 207 = true ∨ valuation q 20 = true ∨ valuation q 52 = true ∨ valuation q 85 = true := by
  rw [value20, value52, value85, value90, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (392 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(136 : Vertex), (264 : Vertex), (384 : Vertex)] := by decide
  have hg := other_cover q (392 : Vertex) (393 : Vertex) [(136 : Vertex), (264 : Vertex), (384 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 21 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value21, value86, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 21 = false ∨ valuation q 86 = false ∨ valuation q 92 = false := by
  rw [value21, value86, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 21 = false ∨ valuation q 86 = false ∨ valuation q 93 = false := by
  rw [value21, value86, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (385 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 21 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value21, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (137 : Vertex) (392 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E207.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112207
