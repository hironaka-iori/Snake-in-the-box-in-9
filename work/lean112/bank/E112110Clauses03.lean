import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value26, value29, value30, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(148 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (145 : Vertex) [(148 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value26, value27, value30, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(145 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (148 : Vertex) [(145 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 144 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value26, value27, value29, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(145 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (152 : Vertex) [(145 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 28 = true := by
  rw [value27, value28, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(147 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (144 : Vertex) [(147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 26 = true := by
  rw [value26, value27, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (147 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (147 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 19 = false ∨ valuation q 27 = false := by
  rw [value19, value27, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (147 : Vertex) (131 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 27 = true := by
  rw [value27, value28, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(145 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (131 : Vertex) [(145 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 19 = true := by
  rw [value19, value28, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (147 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(131 : Vertex)] := by decide
  have hg := other_cover q (147 : Vertex) (145 : Vertex) [(131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 44 = false := by
  rw [value26, value29, value31, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (144 : Vertex) (156 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 31 = true ∨ valuation q 44 = true := by
  rw [value29, value31, value44, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(156 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(156 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 26 = true ∨ valuation q 44 = true := by
  rw [value26, value29, value44, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(144 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (156 : Vertex) [(144 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 26 = true ∨ valuation q 31 = true := by
  rw [value26, value29, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(144 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (212 : Vertex) [(144 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 91 = false := by
  rw [value26, value30, value31, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (152 : Vertex) (144 : Vertex) (156 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 26 = true ∨ valuation q 91 = true := by
  rw [value26, value30, value91, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(144 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (156 : Vertex) [(144 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 26 = true ∨ valuation q 31 = true := by
  rw [value26, value30, value31, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(144 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (408 : Vertex) [(144 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value29, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (148 : Vertex) (152 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 30 = true ∨ valuation q 32 = true := by
  rw [value30, value31, value32, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(152 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (148 : Vertex) [(152 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 29 = true ∨ valuation q 32 = true := by
  rw [value29, value31, value32, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(148 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (152 : Vertex) [(148 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value29, value30, value31, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(148 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (158 : Vertex) [(148 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 33 = true := by
  rw [value32, value33, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (156 : Vertex) [(159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 31 = true := by
  rw [value31, value32, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 25 = false ∨ valuation q 32 = false ∨ valuation q 95 = false := by
  rw [value25, value32, value33, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (159 : Vertex) (143 : Vertex) (158 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 151 = true ∨ valuation q 32 = true ∨ valuation q 95 = true := by
  rw [value32, value33, value95, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(158 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (143 : Vertex) [(158 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 151 = true ∨ valuation q 25 = true ∨ valuation q 95 = true := by
  rw [value25, value33, value95, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(143 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(143 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 96 = false := by
  rw [value34, value35, value38, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 35 = false ∨ valuation q 38 = false := by
  rw [value35, value38, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 38 = true ∨ valuation q 96 = true := by
  rw [value34, value38, value96, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(200 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (193 : Vertex) [(200 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 35 = true ∨ valuation q 96 = true := by
  rw [value34, value35, value96, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(193 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(193 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 35 = true ∨ valuation q 38 = true := by
  rw [value34, value35, value38, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(193 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (448 : Vertex) [(193 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 39 = true ∨ valuation q 97 = true := by
  rw [value35, value39, value97, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(201 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (192 : Vertex) [(201 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 34 = true ∨ valuation q 97 = true := by
  rw [value34, value35, value97, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(192 : Vertex), (449 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (201 : Vertex) [(192 : Vertex), (449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 34 = true ∨ valuation q 39 = true := by
  rw [value34, value35, value39, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (449 : Vertex) [(192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E110.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112110
