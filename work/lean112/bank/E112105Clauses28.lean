import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value83, value117, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value83, value117, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 83 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value83, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (348 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 101 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value101, value110, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 101 = false ∨ valuation q 110 = false ∨ valuation q 122 = false := by
  rw [value101, value110, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (460 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 101 = false ∨ valuation q 110 = false ∨ valuation q 123 = false := by
  rw [value101, value110, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (460 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 101 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value101, value117, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 101 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value101, value117, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 101 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value101, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value110, value117, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (468 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 123 = false := by
  rw [value110, value117, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 110 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value110, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 117 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value117, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (468 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 83 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value83, value101, value110, value117, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(348 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (220 : Vertex) [(348 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 66 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value66, value101, value110, value117, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(220 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (348 : Vertex) [(220 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 66 = true ∨ valuation q 83 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value66, value83, value110, value117, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(220 : Vertex), (348 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (412 : Vertex) [(220 : Vertex), (348 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 66 = true ∨ valuation q 83 = true ∨ valuation q 101 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value66, value83, value101, value117, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(220 : Vertex), (348 : Vertex), (412 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (460 : Vertex) [(220 : Vertex), (348 : Vertex), (412 : Vertex), (468 : Vertex), (477 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 66 = true ∨ valuation q 83 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 122 = true ∨ valuation q 123 = true := by
  rw [value66, value83, value101, value110, value121, value122, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(220 : Vertex), (348 : Vertex), (412 : Vertex), (460 : Vertex), (477 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (468 : Vertex) [(220 : Vertex), (348 : Vertex), (412 : Vertex), (460 : Vertex), (477 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 66 = true ∨ valuation q 83 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value66, value83, value101, value110, value117, value121, value123, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(220 : Vertex), (348 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (477 : Vertex) [(220 : Vertex), (348 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 66 = true ∨ valuation q 83 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 122 = true := by
  rw [value66, value83, value101, value110, value117, value121, value122, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(220 : Vertex), (348 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (478 : Vertex) [(220 : Vertex), (348 : Vertex), (412 : Vertex), (460 : Vertex), (468 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 122 = true := by
  rw [value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (477 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 111 = true ∨ valuation q 118 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value111, value118, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ∈ [(461 : Vertex), (469 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (477 : Vertex) [(461 : Vertex), (469 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 111 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value111, value118, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (461 : Vertex) (469 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 111 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value111, value118, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (461 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 111 = false ∨ valuation q 118 = false := by
  rw [value111, value118, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (477 : Vertex) (461 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide)

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value118, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (477 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide)

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 118 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value118, value121, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(469 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (461 : Vertex) [(469 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 111 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value111, value121, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(461 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (469 : Vertex) [(461 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 111 = true ∨ valuation q 118 = true ∨ valuation q 124 = true := by
  rw [value111, value118, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(461 : Vertex), (469 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (476 : Vertex) [(461 : Vertex), (469 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 111 = true ∨ valuation q 118 = true ∨ valuation q 121 = true := by
  rw [value111, value118, value121, value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(461 : Vertex), (469 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (479 : Vertex) [(461 : Vertex), (469 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 123 = true := by
  rw [value123, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (478 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 112 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value112, value119, value120, value121, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ∈ [(462 : Vertex), (470 : Vertex), (474 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (478 : Vertex) [(462 : Vertex), (470 : Vertex), (474 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block28 (q : Snake 81) (h : Conditions q) : B112E105.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112105
