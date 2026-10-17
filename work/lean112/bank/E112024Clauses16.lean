import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value90, value95, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value90, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value90, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (442 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 95 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value95, value100, value101, value102, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 100 = true ∨ valuation q 103 = true := by
  rw [value90, value95, value100, value102, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (442 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value90, value95, value100, value101, value102, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (447 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value31, value93, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 31 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value31, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value93, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 81 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value81, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 225 = true ∨ valuation q 81 = true ∨ valuation q 105 = true := by
  rw [value81, value104, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(416 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(416 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 82 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value82, value104, value105, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (480 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 82 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value82, value105, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (489 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 226 = true ∨ valuation q 82 = true ∨ valuation q 109 = true ∨ valuation q 113 = true := by
  rw [value82, value105, value109, value113, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(417 : Vertex), (489 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(417 : Vertex), (489 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 226 = true ∨ valuation q 82 = true ∨ valuation q 104 = true ∨ valuation q 113 = true := by
  rw [value82, value104, value105, value113, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (489 : Vertex) [(417 : Vertex), (480 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 226 = true ∨ valuation q 82 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value82, value104, value105, value109, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (497 : Vertex) [(417 : Vertex), (480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 86 = false ∨ valuation q 117 = false := by
  rw [value36, value86, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value36, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value86, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (422 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 228 = true ∨ valuation q 106 = true ∨ valuation q 112 = true := by
  rw [value106, value107, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(486 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (423 : Vertex) [(486 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 228 = true ∨ valuation q 87 = true ∨ valuation q 112 = true := by
  rw [value87, value107, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(423 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(423 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 228 = true ∨ valuation q 87 = true ∨ valuation q 106 = true := by
  rw [value87, value106, value107, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(423 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(423 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value104, value108, value109, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (424 : Vertex) [(480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value88, value108, value109, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(424 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(424 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 88 = true ∨ valuation q 104 = true := by
  rw [value88, value104, value108, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (489 : Vertex) [(424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value105, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value105, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value105, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value108, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value110, value111, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (489 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 230 = true ∨ valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value105, value108, value109, value110, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(481 : Vertex), (488 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (493 : Vertex) [(481 : Vertex), (488 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 90 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value90, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (491 : Vertex) (427 : Vertex) (489 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E024.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112024
