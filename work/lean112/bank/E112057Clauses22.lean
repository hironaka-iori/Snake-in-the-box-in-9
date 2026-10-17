import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 212 = true ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 89 = true := by
  rw [value79, value85, value86, value87, value89, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(272 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (264 : Vertex) [(272 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 212 = true ∨ valuation q 73 = true ∨ valuation q 79 = true ∨ valuation q 86 = true ∨ valuation q 89 = true := by
  rw [value73, value79, value85, value86, value89, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(264 : Vertex), (272 : Vertex), (281 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (282 : Vertex) [(264 : Vertex), (272 : Vertex), (281 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 74 = false ∨ valuation q 85 = false := by
  rw [value16, value74, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 74 = false ∨ valuation q 88 = false := by
  rw [value16, value74, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 74 = false ∨ valuation q 104 = false := by
  rw [value16, value74, value86, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 74 = false ∨ valuation q 122 = false := by
  rw [value16, value74, value86, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value16, value85, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 85 = false ∨ valuation q 104 = false := by
  rw [value16, value85, value86, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 88 = false ∨ valuation q 104 = false := by
  rw [value16, value86, value88, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (283 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 88 = false ∨ valuation q 122 = false := by
  rw [value16, value86, value88, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 16 = false ∨ valuation q 104 = false ∨ valuation q 122 = false := by
  rw [value16, value86, value104, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = false ∨ valuation q 85 = false ∨ valuation q 104 = false := by
  rw [value74, value85, value86, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = false ∨ valuation q 85 = false ∨ valuation q 122 = false := by
  rw [value74, value85, value86, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = false ∨ valuation q 88 = false ∨ valuation q 104 = false := by
  rw [value74, value86, value88, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (283 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = false ∨ valuation q 88 = false ∨ valuation q 122 = false := by
  rw [value74, value86, value88, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = false ∨ valuation q 104 = false ∨ valuation q 122 = false := by
  rw [value74, value86, value104, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 104 = false := by
  rw [value85, value86, value88, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (283 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 122 = false := by
  rw [value85, value86, value88, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 85 = false ∨ valuation q 104 = false ∨ valuation q 122 = false := by
  rw [value85, value86, value104, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 213 = true ∨ valuation q 16 = true ∨ valuation q 74 = true ∨ valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 122 = true := by
  rw [value16, value74, value85, value86, value88, value122, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(25 : Vertex), (265 : Vertex), (280 : Vertex), (283 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (345 : Vertex) [(25 : Vertex), (265 : Vertex), (280 : Vertex), (283 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 214 = true ∨ valuation q 85 = true ∨ valuation q 88 = true := by
  rw [value85, value87, value88, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(280 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (274 : Vertex) [(280 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 214 = true ∨ valuation q 80 = true ∨ valuation q 88 = true := by
  rw [value80, value87, value88, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (280 : Vertex) [(274 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 214 = true ∨ valuation q 80 = true ∨ valuation q 85 = true := by
  rw [value80, value85, value87, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(274 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (283 : Vertex) [(274 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 88 = true := by
  rw [value88, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (283 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 75 = false ∨ valuation q 86 = false := by
  rw [value17, value75, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value17, value75, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 75 = false ∨ valuation q 90 = false := by
  rw [value17, value75, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 75 = false ∨ valuation q 105 = false := by
  rw [value17, value75, value88, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 75 = false ∨ valuation q 123 = false := by
  rw [value17, value75, value88, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value17, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (281 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 90 = false := by
  rw [value17, value86, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (281 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 105 = false := by
  rw [value17, value86, value88, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (281 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E057.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112057
