import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 47 = true ∨ valuation q 78 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value47, value78, value114, value115, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(141 : Vertex), (269 : Vertex), (396 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(141 : Vertex), (269 : Vertex), (396 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 243 = true ∨ valuation q 47 = true ∨ valuation q 78 = true ∨ valuation q 112 = true ∨ valuation q 117 = true := by
  rw [value47, value78, value112, value115, value117, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(141 : Vertex), (269 : Vertex), (389 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (396 : Vertex) [(141 : Vertex), (269 : Vertex), (389 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 116 = true := by
  rw [value116, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (398 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 117 = true ∨ valuation q 126 = true := by
  rw [value113, value114, value116, value117, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ∈ [(394 : Vertex), (396 : Vertex), (399 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (398 : Vertex) [(394 : Vertex), (396 : Vertex), (399 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value113, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (396 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 126 = false := by
  rw [value113, value114, value116, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (396 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 113 = false ∨ valuation q 117 = false ∨ valuation q 126 = false := by
  rw [value113, value116, value117, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (399 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 114 = true ∨ valuation q 117 = true ∨ valuation q 126 = true := by
  rw [value114, value116, value117, value126, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(396 : Vertex), (399 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (394 : Vertex) [(396 : Vertex), (399 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 126 = true := by
  rw [value113, value114, value116, value126, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(394 : Vertex), (396 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (399 : Vertex) [(394 : Vertex), (396 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 244 = true ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value113, value114, value116, value117, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(394 : Vertex), (396 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (414 : Vertex) [(394 : Vertex), (396 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 79 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value79, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 79 = false ∨ valuation q 115 = false ∨ valuation q 127 = false := by
  rw [value79, value115, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (397 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 79 = false ∨ valuation q 116 = false ∨ valuation q 127 = false := by
  rw [value79, value116, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (271 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 127 = false := by
  rw [value115, value116, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (397 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 245 = true ∨ valuation q 79 = true ∨ valuation q 115 = true ∨ valuation q 116 = true := by
  rw [value79, value115, value116, value117, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(271 : Vertex), (397 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (415 : Vertex) [(271 : Vertex), (397 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 48 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value48, value109, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (144 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 80 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value80, value109, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (384 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 246 = true ∨ valuation q 80 = true ∨ valuation q 109 = true ∨ valuation q 119 = true := by
  rw [value80, value109, value118, value119, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(272 : Vertex), (384 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (144 : Vertex) [(272 : Vertex), (384 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 246 = true ∨ valuation q 48 = true ∨ valuation q 80 = true ∨ valuation q 119 = true := by
  rw [value48, value80, value118, value119, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(144 : Vertex), (272 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (384 : Vertex) [(144 : Vertex), (272 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 110 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value110, value118, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 110 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value110, value118, value119, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (400 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 110 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value110, value119, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 118 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value118, value119, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (400 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 118 = true ∨ valuation q 120 = true ∨ valuation q 123 = true := by
  rw [value118, value119, value120, value123, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(400 : Vertex), (403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (385 : Vertex) [(400 : Vertex), (403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 110 = true ∨ valuation q 118 = true ∨ valuation q 123 = true := by
  rw [value110, value118, value119, value123, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(385 : Vertex), (400 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(385 : Vertex), (400 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 247 = true ∨ valuation q 110 = true ∨ valuation q 118 = true ∨ valuation q 120 = true := by
  rw [value110, value118, value119, value120, value247]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(385 : Vertex), (400 : Vertex), (403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (409 : Vertex) [(385 : Vertex), (400 : Vertex), (403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 120 = true := by
  rw [value120, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (403 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 119 = true ∨ valuation q 122 = true ∨ valuation q 124 = true := by
  rw [value119, value120, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ∈ [(401 : Vertex), (407 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (403 : Vertex) [(401 : Vertex), (407 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 119 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value119, value120, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (403 : Vertex) (401 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 248 = true ∨ valuation q 122 = true ∨ valuation q 124 = true := by
  rw [value120, value122, value124, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(407 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(407 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 248 = true ∨ valuation q 119 = true ∨ valuation q 124 = true := by
  rw [value119, value120, value124, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (407 : Vertex) [(401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 248 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value119, value120, value122, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (411 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block27 (q : Snake 81) (h : Conditions q) : B112E055.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112055
