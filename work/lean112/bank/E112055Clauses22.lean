import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 218 = true ∨ valuation q 18 = true ∨ valuation q 77 = true ∨ valuation q 82 = true ∨ valuation q 106 = true ∨ valuation q 125 = true := by
  rw [value18, value77, value82, value90, value106, value125, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(28 : Vertex), (268 : Vertex), (276 : Vertex), (348 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (280 : Vertex) [(28 : Vertex), (268 : Vertex), (276 : Vertex), (348 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value20, value79, value85, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (271 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value20, value79, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (271 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 79 = false ∨ valuation q 108 = false := by
  rw [value20, value79, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (271 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 79 = false ∨ valuation q 127 = false := by
  rw [value20, value79, value91, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (271 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value20, value85, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (279 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 85 = false ∨ valuation q 108 = false := by
  rw [value20, value85, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (279 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 85 = false ∨ valuation q 127 = false := by
  rw [value20, value85, value91, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (279 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value20, value89, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (283 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 89 = false ∨ valuation q 127 = false := by
  rw [value20, value89, value91, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (283 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 20 = false ∨ valuation q 108 = false ∨ valuation q 127 = false := by
  rw [value20, value91, value108, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value79, value85, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 108 = false := by
  rw [value79, value85, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 127 = false := by
  rw [value79, value85, value91, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 79 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value79, value89, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (283 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 79 = false ∨ valuation q 89 = false ∨ valuation q 127 = false := by
  rw [value79, value89, value91, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (283 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 79 = false ∨ valuation q 108 = false ∨ valuation q 127 = false := by
  rw [value79, value91, value108, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 108 = false := by
  rw [value85, value89, value91, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (283 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 127 = false := by
  rw [value85, value89, value91, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (283 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 108 = false ∨ valuation q 127 = false := by
  rw [value85, value91, value108, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 108 = false ∨ valuation q 127 = false := by
  rw [value89, value91, value108, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (283 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value92, value93, value94, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 94 = true ∨ valuation q 100 = true := by
  rw [value92, value94, value100, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(322 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(322 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 93 = true ∨ valuation q 100 = true := by
  rw [value92, value93, value100, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(321 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (322 : Vertex) [(321 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 93 = true ∨ valuation q 94 = true := by
  rw [value92, value93, value94, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(321 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (336 : Vertex) [(321 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 93 = true := by
  rw [value93, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (321 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value92, value93, value95, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 92 = false ∨ valuation q 101 = false := by
  rw [value92, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (321 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 95 = true ∨ valuation q 101 = true := by
  rw [value93, value95, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(325 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(325 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 92 = true ∨ valuation q 101 = true := by
  rw [value92, value93, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(320 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (325 : Vertex) [(320 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 92 = true ∨ valuation q 95 = true := by
  rw [value92, value93, value95, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(320 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(320 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 94 = true := by
  rw [value94, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (322 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block22 (q : Snake 81) (h : Conditions q) : B112E055.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112055
