import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 119 = true ∨ valuation q 123 = true := by
  rw [value118, value119, value123, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(471 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (468 : Vertex) [(471 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 117 = true ∨ valuation q 123 = true := by
  rw [value117, value118, value123, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (471 : Vertex) → w ∈ [(468 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (471 : Vertex) [(468 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 242 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value117, value118, value119, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(468 : Vertex), (471 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (477 : Vertex) [(468 : Vertex), (471 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 119 = true := by
  rw [value119, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (471 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 116 = true ∨ valuation q 118 = true ∨ valuation q 124 = true := by
  rw [value116, value118, value119, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ∈ [(467 : Vertex), (469 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (471 : Vertex) [(467 : Vertex), (469 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 116 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value116, value118, value119, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (467 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value116, value118, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (471 : Vertex) (467 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide)

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value118, value124, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (471 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide)

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 118 = true ∨ valuation q 124 = true := by
  rw [value118, value119, value124, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(469 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (467 : Vertex) [(469 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 116 = true ∨ valuation q 124 = true := by
  rw [value116, value119, value124, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(467 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (469 : Vertex) [(467 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 243 = true ∨ valuation q 116 = true ∨ valuation q 118 = true := by
  rw [value116, value118, value119, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(467 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (479 : Vertex) [(467 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 120 = true := by
  rw [value120, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (472 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 74 = true ∨ valuation q 112 = true ∨ valuation q 121 = true := by
  rw [value74, value112, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ∈ [(216 : Vertex), (456 : Vertex), (474 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (472 : Vertex) [(216 : Vertex), (456 : Vertex), (474 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 74 = false ∨ valuation q 112 = false ∨ valuation q 121 = false := by
  rw [value74, value112, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (216 : Vertex) (456 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 74 = false ∨ valuation q 121 = false := by
  rw [value74, value121, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (472 : Vertex) (216 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide)

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 112 = false ∨ valuation q 121 = false := by
  rw [value112, value121, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (472 : Vertex) (456 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide)

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 112 = true ∨ valuation q 121 = true := by
  rw [value112, value120, value121, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(456 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (216 : Vertex) [(456 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 74 = true ∨ valuation q 121 = true := by
  rw [value74, value120, value121, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(216 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (456 : Vertex) [(216 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 244 = true ∨ valuation q 74 = true ∨ valuation q 112 = true := by
  rw [value74, value112, value120, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(216 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (474 : Vertex) [(216 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 75 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value75, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (472 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 120 = true ∨ valuation q 122 = true := by
  rw [value120, value121, value122, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(472 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (218 : Vertex) [(472 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 75 = true ∨ valuation q 122 = true := by
  rw [value75, value121, value122, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(218 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (472 : Vertex) [(218 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 245 = true ∨ valuation q 75 = true ∨ valuation q 120 = true := by
  rw [value75, value120, value121, value245]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(218 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (475 : Vertex) [(218 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 122 = true := by
  rw [value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (475 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 116 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value116, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ∈ [(467 : Vertex), (474 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (475 : Vertex) [(467 : Vertex), (474 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 116 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value116, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (467 : Vertex) (474 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 116 = false ∨ valuation q 121 = false := by
  rw [value116, value121, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (475 : Vertex) (467 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide)

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value121, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(474 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (467 : Vertex) [(474 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 116 = true ∨ valuation q 124 = true := by
  rw [value116, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(467 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (474 : Vertex) [(467 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 116 = true ∨ valuation q 121 = true := by
  rw [value116, value121, value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(467 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (479 : Vertex) [(467 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 77 = false ∨ valuation q 105 = false ∨ valuation q 118 = false := by
  rw [value77, value105, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (413 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 77 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value77, value118, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E089.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112089
