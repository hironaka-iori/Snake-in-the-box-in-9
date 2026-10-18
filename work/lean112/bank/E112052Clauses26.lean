import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value35, value110, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value35, value110, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value35, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value35, value112, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 35 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value35, value113, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (199 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value71, value90, value110, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 112 = false := by
  rw [value71, value90, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 118 = false := by
  rw [value71, value90, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 90 = false ∨ valuation q 122 = false := by
  rw [value71, value90, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value71, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value71, value110, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value71, value110, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value71, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value71, value112, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 71 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value71, value113, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value90, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 110 = false ∨ valuation q 118 = false := by
  rw [value90, value110, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value90, value110, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value90, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value90, value112, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 90 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value90, value113, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value110, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (453 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 122 = false := by
  rw [value110, value112, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (453 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 110 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value110, value113, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (451 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 112 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value112, value113, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (453 : Vertex) (463 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 92 = false ∨ valuation q 109 = false ∨ valuation q 115 = false := by
  rw [value92, value109, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (449 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 92 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value92, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (459 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 109 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value109, value114, value115, value116, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(449 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (393 : Vertex) [(449 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 92 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value92, value114, value115, value116, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(393 : Vertex), (459 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (449 : Vertex) [(393 : Vertex), (459 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 92 = true ∨ valuation q 109 = true ∨ valuation q 116 = true := by
  rw [value92, value109, value114, value116, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(393 : Vertex), (449 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (459 : Vertex) [(393 : Vertex), (449 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 92 = true ∨ valuation q 109 = true ∨ valuation q 115 = true := by
  rw [value92, value109, value114, value115, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(393 : Vertex), (449 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (461 : Vertex) [(393 : Vertex), (449 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value94, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (395 : Vertex) (451 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E052.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112052
