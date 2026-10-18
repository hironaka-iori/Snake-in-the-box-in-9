import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 228 = true ∨ valuation q 106 = true ∨ valuation q 112 = true := by
  rw [value106, value107, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(486 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (423 : Vertex) [(486 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 228 = true ∨ valuation q 87 = true ∨ valuation q 112 = true := by
  rw [value87, value107, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(423 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(423 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 228 = true ∨ valuation q 87 = true ∨ valuation q 106 = true := by
  rw [value87, value106, value107, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(423 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(423 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value104, value108, value109, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (424 : Vertex) [(480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value88, value108, value109, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(424 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(424 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 229 = true ∨ valuation q 88 = true ∨ valuation q 104 = true := by
  rw [value88, value104, value108, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (489 : Vertex) [(424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value105, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value105, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value105, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value108, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (488 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 230 = true ∨ valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value108, value109, value110, value111, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(488 : Vertex), (491 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (481 : Vertex) [(488 : Vertex), (491 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 231 = true ∨ valuation q 71 = true ∨ valuation q 90 = true ∨ valuation q 109 = true ∨ valuation q 112 = true := by
  rw [value71, value90, value109, value110, value112, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(363 : Vertex), (427 : Vertex), (489 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (235 : Vertex) [(363 : Vertex), (427 : Vertex), (489 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 231 = true ∨ valuation q 38 = true ∨ valuation q 71 = true ∨ valuation q 90 = true ∨ valuation q 109 = true := by
  rw [value38, value71, value90, value109, value110, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(235 : Vertex), (363 : Vertex), (427 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (495 : Vertex) [(235 : Vertex), (363 : Vertex), (427 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value109, value111, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 232 = true ∨ valuation q 112 = true ∨ valuation q 120 = true := by
  rw [value111, value112, value120, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(495 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (489 : Vertex) [(495 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 232 = true ∨ valuation q 109 = true ∨ valuation q 120 = true := by
  rw [value109, value111, value120, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(489 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (495 : Vertex) [(489 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 232 = true ∨ valuation q 109 = true ∨ valuation q 112 = true := by
  rw [value109, value111, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(489 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (509 : Vertex) [(489 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 93 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value93, value107, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 93 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value93, value107, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (487 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 93 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value93, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (431 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value107, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (487 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 233 = true ∨ valuation q 93 = true ∨ valuation q 107 = true ∨ valuation q 110 = true := by
  rw [value93, value107, value110, value112, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(431 : Vertex), (487 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(431 : Vertex), (487 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 94 = false ∨ valuation q 105 = false ∨ valuation q 115 = false := by
  rw [value94, value105, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 234 = true ∨ valuation q 94 = true ∨ valuation q 115 = true := by
  rw [value94, value113, value115, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(433 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (481 : Vertex) [(433 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 234 = true ∨ valuation q 94 = true ∨ valuation q 105 = true := by
  rw [value94, value105, value113, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(433 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (499 : Vertex) [(433 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value114, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (499 : Vertex) (502 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 235 = true ∨ valuation q 117 = true ∨ valuation q 118 = true := by
  rw [value114, value117, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(502 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (499 : Vertex) [(502 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 95 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value95, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (497 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 236 = true ∨ valuation q 113 = true ∨ valuation q 114 = true := by
  rw [value113, value114, value115, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(497 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (435 : Vertex) [(497 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 236 = true ∨ valuation q 95 = true ∨ valuation q 114 = true := by
  rw [value95, value114, value115, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(435 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (497 : Vertex) [(435 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 236 = true ∨ valuation q 95 = true ∨ valuation q 113 = true := by
  rw [value95, value113, value115, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(435 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (498 : Vertex) [(435 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 41 = false ∨ valuation q 96 = false ∨ valuation q 117 = false := by
  rw [value41, value96, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (436 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E026.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112026
