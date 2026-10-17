import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 119 = true ∨ valuation q 124 = true ∨ valuation q 125 = true := by
  rw [value119, value123, value124, value125, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (344 : Vertex) [(464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 80 = true ∨ valuation q 124 = true ∨ valuation q 125 = true := by
  rw [value80, value123, value124, value125, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(344 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(344 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 80 = true ∨ valuation q 119 = true ∨ valuation q 125 = true := by
  rw [value80, value119, value123, value125, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(344 : Vertex), (464 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (474 : Vertex) [(344 : Vertex), (464 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 250 = true ∨ valuation q 80 = true ∨ valuation q 119 = true ∨ valuation q 124 = true := by
  rw [value80, value119, value123, value124, value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(344 : Vertex), (464 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (476 : Vertex) [(344 : Vertex), (464 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 82 = false ∨ valuation q 103 = false := by
  rw [value46, value82, value103, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 82 = false ∨ valuation q 120 = false := by
  rw [value46, value82, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 82 = false ∨ valuation q 123 = false := by
  rw [value46, value82, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 82 = false ∨ valuation q 127 = false := by
  rw [value46, value82, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 103 = false ∨ valuation q 120 = false := by
  rw [value46, value103, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (410 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 103 = false ∨ valuation q 123 = false := by
  rw [value46, value103, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 103 = false ∨ valuation q 127 = false := by
  rw [value46, value103, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value46, value120, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 120 = false ∨ valuation q 127 = false := by
  rw [value46, value120, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 46 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value46, value123, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 103 = false ∨ valuation q 120 = false := by
  rw [value82, value103, value120, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (410 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 103 = false ∨ valuation q 123 = false := by
  rw [value82, value103, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 103 = false ∨ valuation q 127 = false := by
  rw [value82, value103, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value82, value120, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 120 = false ∨ valuation q 127 = false := by
  rw [value82, value120, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 82 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value82, value123, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 103 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value103, value120, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 103 = false ∨ valuation q 120 = false ∨ valuation q 127 = false := by
  rw [value103, value120, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 103 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value103, value123, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 120 = false ∨ valuation q 123 = false ∨ valuation q 127 = false := by
  rw [value120, value123, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (466 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 123 = false ∨ valuation q 126 = false ∨ valuation q 127 = false := by
  rw [value123, value125, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (472 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 126 = false ∨ valuation q 127 = false := by
  rw [value126, value127, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (476 : Vertex) (477 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide)

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 252 = true ∨ valuation q 123 = true ∨ valuation q 127 = true := by
  rw [value123, value125, value127, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(472 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (477 : Vertex) [(472 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 252 = true ∨ valuation q 123 = true ∨ valuation q 126 = true := by
  rw [value123, value125, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(472 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (478 : Vertex) [(472 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 48 = false ∨ valuation q 116 = false ∨ valuation q 125 = false := by
  rw [value48, value116, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 105 = false ∨ valuation q 116 = false ∨ valuation q 125 = false := by
  rw [value105, value116, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (413 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 253 = true ∨ valuation q 105 = true ∨ valuation q 116 = true ∨ valuation q 125 = true := by
  rw [value105, value116, value125, value126, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(413 : Vertex), (461 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (221 : Vertex) [(413 : Vertex), (461 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 253 = true ∨ valuation q 48 = true ∨ valuation q 116 = true ∨ valuation q 125 = true := by
  rw [value48, value116, value125, value126, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(221 : Vertex), (461 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (413 : Vertex) [(221 : Vertex), (461 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block29 (q : Snake 81) (h : Conditions q) : B112E052.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112052
