import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 223 = true ∨ valuation q 55 = true ∨ valuation q 100 = true := by
  rw [value55, value100, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(190 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (430 : Vertex) [(190 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 223 = true ∨ valuation q 55 = true ∨ valuation q 93 = true := by
  rw [value55, value93, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(190 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (442 : Vertex) [(190 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value84, value104, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value84, value104, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 84 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value84, value104, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 224 = true ∨ valuation q 84 = true ∨ valuation q 106 = true ∨ valuation q 109 = true := by
  rw [value84, value104, value106, value109, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(416 : Vertex), (482 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(416 : Vertex), (482 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 224 = true ∨ valuation q 84 = true ∨ valuation q 105 = true ∨ valuation q 109 = true := by
  rw [value84, value104, value105, value109, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(416 : Vertex), (481 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (482 : Vertex) [(416 : Vertex), (481 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 224 = true ∨ valuation q 84 = true ∨ valuation q 105 = true ∨ valuation q 106 = true := by
  rw [value84, value104, value105, value106, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(416 : Vertex), (481 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(416 : Vertex), (481 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 225 = true ∨ valuation q 107 = true := by
  rw [value105, value107, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(483 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 225 = true ∨ valuation q 104 = true := by
  rw [value104, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(480 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (483 : Vertex) [(480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 57 = false ∨ valuation q 107 = false ∨ valuation q 113 = false := by
  rw [value57, value106, value107, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (226 : Vertex) (483 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 226 = true ∨ valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 113 = true := by
  rw [value104, value106, value107, value113, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(480 : Vertex), (483 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (226 : Vertex) [(480 : Vertex), (483 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 226 = true ∨ valuation q 57 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value57, value104, value106, value107, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(226 : Vertex), (480 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (498 : Vertex) [(226 : Vertex), (480 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value105, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (482 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 114 = false := by
  rw [value105, value107, value108, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 114 = false := by
  rw [value106, value107, value108, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (487 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value105, value108, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (483 : Vertex) (481 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 227 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 114 = true := by
  rw [value106, value107, value108, value114, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (483 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(482 : Vertex), (487 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (483 : Vertex) (481 : Vertex) [(482 : Vertex), (487 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 227 = true ∨ valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value105, value106, value107, value114, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (483 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(481 : Vertex), (482 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (483 : Vertex) (487 : Vertex) [(481 : Vertex), (482 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value88, value107, value108, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (483 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 228 = true ∨ valuation q 88 = true ∨ valuation q 112 = true := by
  rw [value88, value108, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(423 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (483 : Vertex) [(423 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 228 = true ∨ valuation q 88 = true ∨ valuation q 107 = true := by
  rw [value88, value107, value108, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(423 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(423 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 79 = false ∨ valuation q 89 = false ∨ valuation q 104 = false := by
  rw [value79, value89, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 79 = false ∨ valuation q 104 = false ∨ valuation q 110 = false := by
  rw [value79, value104, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (360 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 89 = false ∨ valuation q 104 = false ∨ valuation q 110 = false := by
  rw [value89, value104, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (488 : Vertex) (424 : Vertex) (480 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 229 = true ∨ valuation q 89 = true ∨ valuation q 104 = true ∨ valuation q 110 = true := by
  rw [value89, value104, value109, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (360 : Vertex) [(424 : Vertex), (480 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 229 = true ∨ valuation q 79 = true ∨ valuation q 104 = true ∨ valuation q 110 = true := by
  rw [value79, value104, value109, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(360 : Vertex), (480 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (424 : Vertex) [(360 : Vertex), (480 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 229 = true ∨ valuation q 79 = true ∨ valuation q 89 = true ∨ valuation q 110 = true := by
  rw [value79, value89, value109, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(360 : Vertex), (424 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(360 : Vertex), (424 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 64 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value64, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 64 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value64, value109, value110, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 64 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value64, value110, value111, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (236 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value109, value110, value111, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (488 : Vertex) (493 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E004.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112004
