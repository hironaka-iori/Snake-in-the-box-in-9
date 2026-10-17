import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 18 = false ∨ valuation q 85 = false ∨ valuation q 124 = false := by
  rw [value18, value85, value89, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (28 : Vertex) (280 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value76, value81, value85, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (268 : Vertex) (276 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 106 = false := by
  rw [value81, value85, value89, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (276 : Vertex) (280 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 124 = false := by
  rw [value81, value85, value89, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (276 : Vertex) (280 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 85 = false ∨ valuation q 106 = false ∨ valuation q 124 = false := by
  rw [value85, value89, value106, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (280 : Vertex) (348 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 76 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 106 = true ∨ valuation q 124 = true := by
  rw [value76, value81, value85, value89, value106, value124, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(268 : Vertex), (276 : Vertex), (280 : Vertex), (348 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (28 : Vertex) [(268 : Vertex), (276 : Vertex), (280 : Vertex), (348 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 18 = true ∨ valuation q 76 = true ∨ valuation q 85 = true ∨ valuation q 106 = true ∨ valuation q 124 = true := by
  rw [value18, value76, value85, value89, value106, value124, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(28 : Vertex), (268 : Vertex), (280 : Vertex), (348 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (276 : Vertex) [(28 : Vertex), (268 : Vertex), (280 : Vertex), (348 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 18 = true ∨ valuation q 76 = true ∨ valuation q 81 = true ∨ valuation q 106 = true ∨ valuation q 124 = true := by
  rw [value18, value76, value81, value89, value106, value124, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(28 : Vertex), (268 : Vertex), (276 : Vertex), (348 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (280 : Vertex) [(28 : Vertex), (268 : Vertex), (276 : Vertex), (348 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 18 = true ∨ valuation q 76 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 124 = true := by
  rw [value18, value76, value81, value85, value89, value124, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(28 : Vertex), (268 : Vertex), (276 : Vertex), (280 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (348 : Vertex) [(28 : Vertex), (268 : Vertex), (276 : Vertex), (280 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 216 = true ∨ valuation q 18 = true ∨ valuation q 76 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 106 = true := by
  rw [value18, value76, value81, value85, value89, value106, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(28 : Vertex), (268 : Vertex), (276 : Vertex), (280 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (412 : Vertex) [(28 : Vertex), (268 : Vertex), (276 : Vertex), (280 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 78 = false ∨ valuation q 108 = false := by
  rw [value20, value78, value90, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (271 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 20 = false ∨ valuation q 88 = false ∨ valuation q 108 = false := by
  rw [value20, value88, value90, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (31 : Vertex) (283 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 84 = false ∨ valuation q 88 = false := by
  rw [value78, value84, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (279 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 108 = false := by
  rw [value78, value88, value90, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (283 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 126 = false := by
  rw [value78, value88, value90, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (283 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 78 = false ∨ valuation q 108 = false ∨ valuation q 126 = false := by
  rw [value78, value90, value108, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (271 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 88 = false ∨ valuation q 108 = false ∨ valuation q 126 = false := by
  rw [value88, value90, value108, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (283 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 78 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 108 = true ∨ valuation q 126 = true := by
  rw [value78, value84, value88, value90, value108, value126, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(271 : Vertex), (279 : Vertex), (283 : Vertex), (351 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (31 : Vertex) [(271 : Vertex), (279 : Vertex), (283 : Vertex), (351 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 20 = true ∨ valuation q 78 = true ∨ valuation q 84 = true ∨ valuation q 108 = true ∨ valuation q 126 = true := by
  rw [value20, value78, value84, value90, value108, value126, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(31 : Vertex), (271 : Vertex), (279 : Vertex), (351 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (283 : Vertex) [(31 : Vertex), (271 : Vertex), (279 : Vertex), (351 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 217 = true ∨ valuation q 20 = true ∨ valuation q 78 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 126 = true := by
  rw [value20, value78, value84, value88, value90, value126, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (351 : Vertex) → w ∈ [(31 : Vertex), (271 : Vertex), (279 : Vertex), (283 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (351 : Vertex) [(31 : Vertex), (271 : Vertex), (279 : Vertex), (283 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 100 = false := by
  rw [value91, value92, value93, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 93 = true ∨ valuation q 100 = true := by
  rw [value91, value93, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(322 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(322 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 92 = true ∨ valuation q 100 = true := by
  rw [value91, value92, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(321 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (322 : Vertex) [(321 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 218 = true ∨ valuation q 92 = true ∨ valuation q 93 = true := by
  rw [value91, value92, value93, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(321 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (336 : Vertex) [(321 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value91, value92, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (323 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value91, value92, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (323 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value91, value92, value95, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (320 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value92, value94, value95, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (321 : Vertex) (323 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value95, value101, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (321 : Vertex) (325 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 219 = true ∨ valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 95 = true := by
  rw [value91, value92, value94, value95, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(320 : Vertex), (323 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (337 : Vertex) [(320 : Vertex), (323 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value91, value93, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (323 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value91, value94, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (322 : Vertex) (320 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E057.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112057
