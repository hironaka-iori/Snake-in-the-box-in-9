import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 90 = true ∨ valuation q 114 = true ∨ valuation q 126 = true := by
  rw [value90, value114, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ∈ [(284 : Vertex), (396 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (412 : Vertex) [(284 : Vertex), (396 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 90 = false ∨ valuation q 114 = false := by
  rw [value90, value114, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (412 : Vertex) (284 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide)

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 114 = true ∨ valuation q 126 = true := by
  rw [value114, value125, value126, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(396 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (284 : Vertex) [(396 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 90 = true ∨ valuation q 126 = true := by
  rw [value90, value125, value126, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(284 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(284 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 253 = true ∨ valuation q 90 = true ∨ valuation q 114 = true := by
  rw [value90, value114, value125, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(284 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(284 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 55 = false ∨ valuation q 116 = false ∨ valuation q 121 = false := by
  rw [value55, value116, value121, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 55 = false ∨ valuation q 116 = false ∨ valuation q 125 = false := by
  rw [value55, value116, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 55 = false ∨ valuation q 116 = false ∨ valuation q 127 = false := by
  rw [value55, value116, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (398 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 55 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value55, value121, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 55 = false ∨ valuation q 121 = false ∨ valuation q 127 = false := by
  rw [value55, value121, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 55 = false ∨ valuation q 125 = false ∨ valuation q 127 = false := by
  rw [value55, value125, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (158 : Vertex) (412 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 116 = false ∨ valuation q 121 = false ∨ valuation q 125 = false := by
  rw [value116, value121, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 116 = false ∨ valuation q 121 = false ∨ valuation q 127 = false := by
  rw [value116, value121, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 116 = false ∨ valuation q 125 = false ∨ valuation q 127 = false := by
  rw [value116, value125, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (412 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 121 = false ∨ valuation q 125 = false ∨ valuation q 127 = false := by
  rw [value121, value125, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (412 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 91 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 124 = true ∨ valuation q 126 = true := by
  rw [value91, value117, value122, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ∈ [(287 : Vertex), (399 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (415 : Vertex) [(287 : Vertex), (399 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 91 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value91, value122, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 91 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value91, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (287 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 117 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value117, value122, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 117 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value117, value124, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (399 : Vertex) (411 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 124 = true ∨ valuation q 126 = true := by
  rw [value117, value122, value124, value126, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(399 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (287 : Vertex) [(399 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 91 = true ∨ valuation q 122 = true ∨ valuation q 124 = true ∨ valuation q 126 = true := by
  rw [value91, value122, value124, value126, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(287 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (399 : Vertex) [(287 : Vertex), (407 : Vertex), (411 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 91 = true ∨ valuation q 117 = true ∨ valuation q 124 = true ∨ valuation q 126 = true := by
  rw [value91, value117, value124, value126, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(287 : Vertex), (399 : Vertex), (411 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (407 : Vertex) [(287 : Vertex), (399 : Vertex), (411 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 91 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 126 = true := by
  rw [value91, value117, value122, value126, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(287 : Vertex), (399 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (411 : Vertex) [(287 : Vertex), (399 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 255 = true ∨ valuation q 91 = true ∨ valuation q 117 = true ∨ valuation q 122 = true ∨ valuation q 124 = true := by
  rw [value91, value117, value122, value124, value127, value255]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(287 : Vertex), (399 : Vertex), (407 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (414 : Vertex) [(287 : Vertex), (399 : Vertex), (407 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 67 = true := by
  rw [value67, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ∈ [(229 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (485 : Vertex) [(229 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 128 = true := by
  rw [value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (0 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (5 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (10 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 135 = false := by
  rw [value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (12 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 137 = false := by
  rw [value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (15 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block29 (q : Snake 81) (h : Conditions q) : B112E055.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112055
