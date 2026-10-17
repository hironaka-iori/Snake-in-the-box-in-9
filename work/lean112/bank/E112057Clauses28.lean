import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 76 = false ∨ valuation q 115 = false ∨ valuation q 124 = false := by
  rw [value76, value114, value115, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (268 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value114, value115, value116, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (396 : Vertex) (397 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 76 = true ∨ valuation q 116 = true ∨ valuation q 124 = true := by
  rw [value76, value114, value116, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(268 : Vertex), (398 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (397 : Vertex) [(268 : Vertex), (398 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 76 = true ∨ valuation q 115 = true ∨ valuation q 124 = true := by
  rw [value76, value114, value115, value124, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(268 : Vertex), (397 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (398 : Vertex) [(268 : Vertex), (397 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 241 = true ∨ valuation q 76 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value76, value114, value115, value116, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (396 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(268 : Vertex), (397 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (396 : Vertex) (412 : Vertex) [(268 : Vertex), (397 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 47 = false ∨ valuation q 77 = false ∨ valuation q 112 = false := by
  rw [value47, value77, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 47 = false ∨ valuation q 77 = false ∨ valuation q 114 = false := by
  rw [value47, value77, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (269 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 47 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value47, value112, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (389 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 77 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value77, value112, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (389 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 77 = true ∨ valuation q 112 = true ∨ valuation q 114 = true := by
  rw [value77, value112, value114, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(269 : Vertex), (389 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (141 : Vertex) [(269 : Vertex), (389 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 47 = true ∨ valuation q 77 = true ∨ valuation q 114 = true := by
  rw [value47, value77, value114, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(141 : Vertex), (269 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(141 : Vertex), (269 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 242 = true ∨ valuation q 47 = true ∨ valuation q 77 = true ∨ valuation q 112 = true := by
  rw [value47, value77, value112, value115, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(141 : Vertex), (269 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(141 : Vertex), (269 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 125 = false := by
  rw [value113, value114, value116, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (396 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 243 = true ∨ valuation q 114 = true ∨ valuation q 125 = true := by
  rw [value114, value116, value125, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(396 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (394 : Vertex) [(396 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 48 = false ∨ valuation q 79 = false ∨ valuation q 109 = false := by
  rw [value48, value79, value109, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (272 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 48 = false ∨ valuation q 79 = false ∨ valuation q 118 = false := by
  rw [value48, value79, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (272 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 48 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value48, value109, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 79 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value79, value109, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 122 = false := by
  rw [value110, value117, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (400 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 110 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value110, value118, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value117, value118, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (400 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value117, value118, value119, value122, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(400 : Vertex), (403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (385 : Vertex) [(400 : Vertex), (403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value110, value118, value119, value122, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(385 : Vertex), (403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (400 : Vertex) [(385 : Vertex), (403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 122 = true := by
  rw [value110, value117, value118, value122, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(385 : Vertex), (400 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(385 : Vertex), (400 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 245 = true ∨ valuation q 110 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value110, value117, value118, value119, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(385 : Vertex), (400 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (409 : Vertex) [(385 : Vertex), (400 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 118 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value118, value119, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 246 = true ∨ valuation q 118 = true ∨ valuation q 123 = true := by
  rw [value118, value119, value123, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (407 : Vertex) [(401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 246 = true ∨ valuation q 118 = true ∨ valuation q 121 = true := by
  rw [value118, value119, value121, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (411 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 51 = false ∨ valuation q 83 = false ∨ valuation q 121 = false := by
  rw [value51, value83, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (150 : Vertex) (278 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 51 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value51, value120, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (150 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 83 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value83, value120, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (278 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 247 = true ∨ valuation q 51 = true ∨ valuation q 83 = true ∨ valuation q 125 = true := by
  rw [value51, value83, value120, value125, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(150 : Vertex), (278 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (407 : Vertex) [(150 : Vertex), (278 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block28 (q : Snake 81) (h : Conditions q) : B112E057.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112057
