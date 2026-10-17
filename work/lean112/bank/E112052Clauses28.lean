import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 108 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value108, value119, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (448 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 246 = true ∨ valuation q 108 = true ∨ valuation q 123 = true := by
  rw [value108, value119, value123, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(448 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (466 : Vertex) [(448 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 246 = true ∨ valuation q 108 = true ∨ valuation q 120 = true := by
  rw [value108, value119, value120, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(448 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(448 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 119 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value119, value120, value121, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (464 : Vertex) (467 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value120, value121, value124, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(467 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (464 : Vertex) [(467 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 119 = true ∨ valuation q 124 = true := by
  rw [value119, value120, value124, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(464 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (467 : Vertex) [(464 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value119, value120, value121, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (474 : Vertex) [(464 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 121 = true := by
  rw [value121, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (467 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = true ∨ valuation q 120 = true ∨ valuation q 122 = true := by
  rw [value110, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ∈ [(451 : Vertex), (466 : Vertex), (471 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (467 : Vertex) [(451 : Vertex), (466 : Vertex), (471 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value110, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (466 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value120, value122, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (467 : Vertex) (466 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide)

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 120 = true ∨ valuation q 122 = true := by
  rw [value120, value121, value122, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(466 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (451 : Vertex) [(466 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 110 = true ∨ valuation q 122 = true := by
  rw [value110, value121, value122, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(451 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (466 : Vertex) [(451 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 110 = true ∨ valuation q 120 = true := by
  rw [value110, value120, value121, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (471 : Vertex) → w ∈ [(451 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (471 : Vertex) [(451 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 44 = false ∨ valuation q 79 = false ∨ valuation q 113 = false := by
  rw [value44, value79, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (343 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 44 = false ∨ valuation q 79 = false ∨ valuation q 121 = false := by
  rw [value44, value79, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (343 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 44 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value44, value101, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (407 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 44 = false ∨ valuation q 101 = false ∨ valuation q 121 = false := by
  rw [value44, value101, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 44 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value44, value113, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 79 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value79, value101, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (343 : Vertex) (407 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 79 = false ∨ valuation q 101 = false ∨ valuation q 121 = false := by
  rw [value79, value101, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (343 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 79 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value79, value113, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (343 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 101 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value101, value113, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (407 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 79 = true ∨ valuation q 101 = true ∨ valuation q 113 = true ∨ valuation q 121 = true := by
  rw [value79, value101, value113, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(343 : Vertex), (407 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (215 : Vertex) [(343 : Vertex), (407 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 44 = true ∨ valuation q 101 = true ∨ valuation q 113 = true ∨ valuation q 121 = true := by
  rw [value44, value101, value113, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(215 : Vertex), (407 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (343 : Vertex) [(215 : Vertex), (407 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 44 = true ∨ valuation q 79 = true ∨ valuation q 113 = true ∨ valuation q 121 = true := by
  rw [value44, value79, value113, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(215 : Vertex), (343 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (407 : Vertex) [(215 : Vertex), (343 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 44 = true ∨ valuation q 79 = true ∨ valuation q 101 = true ∨ valuation q 121 = true := by
  rw [value44, value79, value101, value121, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(215 : Vertex), (343 : Vertex), (407 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (455 : Vertex) [(215 : Vertex), (343 : Vertex), (407 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 44 = true ∨ valuation q 79 = true ∨ valuation q 101 = true ∨ valuation q 113 = true := by
  rw [value44, value79, value101, value113, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(215 : Vertex), (343 : Vertex), (407 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (467 : Vertex) [(215 : Vertex), (343 : Vertex), (407 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 80 = false ∨ valuation q 119 = false ∨ valuation q 124 = false := by
  rw [value80, value119, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 80 = false ∨ valuation q 119 = false ∨ valuation q 125 = false := by
  rw [value80, value119, value123, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (464 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 80 = false ∨ valuation q 124 = false ∨ valuation q 125 = false := by
  rw [value80, value123, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 119 = false ∨ valuation q 124 = false ∨ valuation q 125 = false := by
  rw [value119, value123, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (464 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E052.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112052
