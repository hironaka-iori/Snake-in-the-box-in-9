import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 102 = false := by
  rw [value92, value93, value94, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 96 = false ∨ valuation q 102 = false := by
  rw [value92, value94, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (481 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 102 = false := by
  rw [value93, value94, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (482 : Vertex) (491 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 48 = false ∨ valuation q 82 = false ∨ valuation q 92 = false := by
  rw [value48, value82, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 48 = false ∨ valuation q 82 = false ∨ valuation q 97 = false := by
  rw [value48, value82, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (421 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 48 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value48, value92, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (229 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 82 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value82, value92, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (485 : Vertex) (421 : Vertex) (481 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 204 = true ∨ valuation q 50 = true ∨ valuation q 94 = true ∨ valuation q 98 = true := by
  rw [value50, value94, value96, value98, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (491 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(235 : Vertex), (483 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (491 : Vertex) (427 : Vertex) [(235 : Vertex), (483 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 205 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value97, value98, value106, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(495 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (493 : Vertex) (485 : Vertex) [(495 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 108 = false := by
  rw [value96, value97, value98, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (491 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 206 = true ∨ valuation q 97 = true ∨ valuation q 108 = true := by
  rw [value97, value98, value108, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(493 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (491 : Vertex) [(493 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 92 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value92, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 93 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value93, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 93 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value93, value99, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 93 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value93, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value99, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (496 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 210 = true ∨ valuation q 94 = true ∨ valuation q 101 = true := by
  rw [value94, value101, value102, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(483 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (497 : Vertex) [(483 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 210 = true ∨ valuation q 94 = true ∨ valuation q 100 = true := by
  rw [value94, value100, value102, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(483 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (498 : Vertex) [(483 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 211 = true ∨ valuation q 107 = true := by
  rw [value103, value107, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (498 : Vertex) [(510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 211 = true ∨ valuation q 101 = true := by
  rw [value101, value103, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(498 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (510 : Vertex) [(498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 57 = false ∨ valuation q 99 = false ∨ valuation q 105 = false := by
  rw [value57, value99, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 97 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value97, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (493 : Vertex) (508 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value103, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (510 : Vertex) (502 : Vertex) (508 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 115 = false := by
  rw [value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (44 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 120 = false := by
  rw [value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (55 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 121 = false := by
  rw [value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (56 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (115 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 133 = false := by
  rw [value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (118 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (140 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 148 = false := by
  rw [value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (151 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 149 = false := by
  rw [value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (152 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 156 = false := by
  rw [value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (229 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block3 (q : Snake 81) (h : Conditions q) : B112E190.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112190
