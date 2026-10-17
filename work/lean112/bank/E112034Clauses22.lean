import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 107 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value107, value115, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (482 : Vertex) (494 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 113 = false ∨ valuation q 118 = false ∨ valuation q 126 = false := by
  rw [value113, value115, value118, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (490 : Vertex) (488 : Vertex) (494 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 74 = true ∨ valuation q 93 = true ∨ valuation q 107 = true ∨ valuation q 113 = true ∨ valuation q 118 = true ∨ valuation q 126 = true := by
  rw [value74, value93, value107, value113, value115, value118, value126, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(362 : Vertex), (426 : Vertex), (482 : Vertex), (488 : Vertex), (494 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (234 : Vertex) [(362 : Vertex), (426 : Vertex), (482 : Vertex), (488 : Vertex), (494 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 37 = true ∨ valuation q 74 = true ∨ valuation q 93 = true ∨ valuation q 107 = true ∨ valuation q 118 = true ∨ valuation q 126 = true := by
  rw [value37, value74, value93, value107, value115, value118, value126, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(234 : Vertex), (362 : Vertex), (426 : Vertex), (482 : Vertex), (494 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (488 : Vertex) [(234 : Vertex), (362 : Vertex), (426 : Vertex), (482 : Vertex), (494 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 37 = true ∨ valuation q 74 = true ∨ valuation q 93 = true ∨ valuation q 107 = true ∨ valuation q 113 = true ∨ valuation q 126 = true := by
  rw [value37, value74, value93, value107, value113, value115, value126, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(234 : Vertex), (362 : Vertex), (426 : Vertex), (482 : Vertex), (488 : Vertex), (506 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (494 : Vertex) [(234 : Vertex), (362 : Vertex), (426 : Vertex), (482 : Vertex), (488 : Vertex), (506 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 37 = true ∨ valuation q 74 = true ∨ valuation q 93 = true ∨ valuation q 107 = true ∨ valuation q 113 = true ∨ valuation q 118 = true := by
  rw [value37, value74, value93, value107, value113, value115, value118, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (490 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(234 : Vertex), (362 : Vertex), (426 : Vertex), (482 : Vertex), (488 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (490 : Vertex) (506 : Vertex) [(234 : Vertex), (362 : Vertex), (426 : Vertex), (482 : Vertex), (488 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value109, value113, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (484 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value109, value113, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (484 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 109 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value109, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (484 : Vertex) (493 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 113 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value113, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (488 : Vertex) (493 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value109, value118, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (492 : Vertex) (484 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value113, value118, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (492 : Vertex) (488 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 109 = true ∨ valuation q 117 = true ∨ valuation q 118 = true := by
  rw [value109, value116, value117, value118, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(484 : Vertex), (493 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (488 : Vertex) [(484 : Vertex), (493 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 109 = true ∨ valuation q 113 = true ∨ valuation q 117 = true := by
  rw [value109, value113, value116, value117, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (492 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(484 : Vertex), (488 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (492 : Vertex) (494 : Vertex) [(484 : Vertex), (488 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 76 = false ∨ valuation q 110 = false := by
  rw [value39, value76, value110, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (365 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value39, value94, value110, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (429 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value39, value94, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (429 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 94 = false ∨ valuation q 128 = false := by
  rw [value39, value94, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (429 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value39, value110, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (485 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 110 = false ∨ valuation q 116 = false := by
  rw [value39, value110, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 110 = false ∨ valuation q 128 = false := by
  rw [value39, value110, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (485 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value39, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (489 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 114 = false ∨ valuation q 128 = false := by
  rw [value39, value114, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (489 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 39 = false ∨ valuation q 116 = false ∨ valuation q 128 = false := by
  rw [value39, value116, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (237 : Vertex) (492 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 94 = false ∨ valuation q 110 = false := by
  rw [value76, value94, value110, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (429 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 110 = false ∨ valuation q 116 = false := by
  rw [value76, value110, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 114 = false ∨ valuation q 128 = false := by
  rw [value76, value114, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (489 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 116 = false ∨ valuation q 128 = false := by
  rw [value76, value116, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (365 : Vertex) (492 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 116 = false := by
  rw [value94, value110, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (429 : Vertex) (485 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 128 = false := by
  rw [value94, value110, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (429 : Vertex) (485 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 128 = false := by
  rw [value94, value114, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (429 : Vertex) (489 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 116 = false ∨ valuation q 128 = false := by
  rw [value94, value116, value117, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (429 : Vertex) (492 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E034.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112034
