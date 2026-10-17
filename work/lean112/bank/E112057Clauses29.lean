import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 84 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value84, value119, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (279 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 84 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 126 = true := by
  rw [value84, value119, value120, value121, value126, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(279 : Vertex), (403 : Vertex), (406 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (151 : Vertex) [(279 : Vertex), (403 : Vertex), (406 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 52 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 126 = true := by
  rw [value52, value119, value120, value121, value126, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(151 : Vertex), (403 : Vertex), (406 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (279 : Vertex) [(151 : Vertex), (403 : Vertex), (406 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 52 = true ∨ valuation q 84 = true ∨ valuation q 120 = true ∨ valuation q 126 = true := by
  rw [value52, value84, value120, value121, value126, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (406 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (403 : Vertex) [(151 : Vertex), (279 : Vertex), (406 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 52 = true ∨ valuation q 84 = true ∨ valuation q 119 = true ∨ valuation q 126 = true := by
  rw [value52, value84, value119, value121, value126, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (403 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (406 : Vertex) [(151 : Vertex), (279 : Vertex), (403 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 248 = true ∨ valuation q 52 = true ∨ valuation q 84 = true ∨ valuation q 119 = true ∨ valuation q 120 = true := by
  rw [value52, value84, value119, value120, value121, value248]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (407 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(151 : Vertex), (279 : Vertex), (403 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (407 : Vertex) (415 : Vertex) [(151 : Vertex), (279 : Vertex), (403 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 122 = true := by
  rw [value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (409 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 86 = true ∨ valuation q 118 = true ∨ valuation q 123 = true := by
  rw [value86, value118, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ∈ [(281 : Vertex), (401 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (409 : Vertex) [(281 : Vertex), (401 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 86 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value86, value118, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (281 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 118 = false ∨ valuation q 123 = false := by
  rw [value118, value123, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (409 : Vertex) (401 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide)

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 86 = true ∨ valuation q 123 = true := by
  rw [value86, value122, value123, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(281 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(281 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 249 = true ∨ valuation q 86 = true ∨ valuation q 118 = true := by
  rw [value86, value118, value122, value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(281 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(281 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 88 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value88, value119, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 88 = false ∨ valuation q 119 = false ∨ valuation q 126 = false := by
  rw [value88, value119, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (403 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 88 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value88, value122, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (283 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 119 = false ∨ valuation q 122 = false ∨ valuation q 126 = false := by
  rw [value119, value122, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 119 = true ∨ valuation q 122 = true ∨ valuation q 126 = true := by
  rw [value119, value122, value123, value126, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(403 : Vertex), (409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (283 : Vertex) [(403 : Vertex), (409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 88 = true ∨ valuation q 122 = true ∨ valuation q 126 = true := by
  rw [value88, value122, value123, value126, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(283 : Vertex), (409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (403 : Vertex) [(283 : Vertex), (409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 88 = true ∨ valuation q 119 = true ∨ valuation q 126 = true := by
  rw [value88, value119, value123, value126, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(283 : Vertex), (403 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (409 : Vertex) [(283 : Vertex), (403 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 88 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value88, value119, value122, value123, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(283 : Vertex), (403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (415 : Vertex) [(283 : Vertex), (403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 89 = false ∨ valuation q 114 = false ∨ valuation q 125 = false := by
  rw [value89, value114, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (284 : Vertex) (396 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 114 = false ∨ valuation q 125 = false := by
  rw [value114, value125, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (412 : Vertex) (396 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide)

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 251 = true ∨ valuation q 89 = true ∨ valuation q 125 = true := by
  rw [value89, value124, value125, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(284 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(284 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 55 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value55, value116, value120, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 55 = false ∨ valuation q 116 = false ∨ valuation q 124 = false := by
  rw [value55, value116, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 116 = false ∨ valuation q 120 = false ∨ valuation q 124 = false := by
  rw [value116, value120, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 116 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value116, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (412 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 252 = true ∨ valuation q 116 = true ∨ valuation q 120 = true ∨ valuation q 124 = true ∨ valuation q 126 = true := by
  rw [value116, value120, value124, value125, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(398 : Vertex), (406 : Vertex), (412 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (158 : Vertex) [(398 : Vertex), (406 : Vertex), (412 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 252 = true ∨ valuation q 55 = true ∨ valuation q 120 = true ∨ valuation q 124 = true ∨ valuation q 126 = true := by
  rw [value55, value120, value124, value125, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (398 : Vertex) → w ∈ [(158 : Vertex), (406 : Vertex), (412 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (398 : Vertex) [(158 : Vertex), (406 : Vertex), (412 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 252 = true ∨ valuation q 55 = true ∨ valuation q 116 = true ∨ valuation q 120 = true ∨ valuation q 126 = true := by
  rw [value55, value116, value120, value125, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(158 : Vertex), (398 : Vertex), (406 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (412 : Vertex) [(158 : Vertex), (398 : Vertex), (406 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 90 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value90, value121, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 90 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value90, value121, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E057.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112057
