import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 36 = false ∨ valuation q 69 = false := by
  rw [value17, value20, value36, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (108 : Vertex) (104 : Vertex) (236 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 36 = false ∨ valuation q 69 = false := by
  rw [value20, value21, value36, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (108 : Vertex) (110 : Vertex) (236 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 18 = true ∨ valuation q 20 = true := by
  rw [value18, value20, value21, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (102 : Vertex) → w ∈ [(106 : Vertex), (108 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (102 : Vertex) [(106 : Vertex), (108 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 16 = true ∨ valuation q 20 = true := by
  rw [value16, value20, value21, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(102 : Vertex), (108 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (106 : Vertex) [(102 : Vertex), (108 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 139 = true ∨ valuation q 16 = true ∨ valuation q 18 = true := by
  rw [value16, value18, value21, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(102 : Vertex), (106 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (108 : Vertex) [(102 : Vertex), (106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 22 = true := by
  rw [value22, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (113 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value8, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (115 : Vertex) (117 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 28 = false := by
  rw [value8, value22, value23, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (115 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 39 = false := by
  rw [value8, value22, value23, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (115 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 72 = false := by
  rw [value8, value22, value23, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (115 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 8 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value8, value22, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (117 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 8 = false ∨ valuation q 28 = false ∨ valuation q 39 = false := by
  rw [value8, value22, value28, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (121 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 8 = false ∨ valuation q 28 = false ∨ valuation q 72 = false := by
  rw [value8, value22, value28, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (49 : Vertex) (121 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 28 = false := by
  rw [value22, value23, value24, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (113 : Vertex) (115 : Vertex) (117 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 22 = true ∨ valuation q 29 = true := by
  rw [value22, value23, value29, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(113 : Vertex), (123 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (119 : Vertex) [(113 : Vertex), (123 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 22 = true ∨ valuation q 26 = true := by
  rw [value22, value23, value26, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(113 : Vertex), (119 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (123 : Vertex) [(113 : Vertex), (119 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 142 = true ∨ valuation q 22 = true ∨ valuation q 26 = true := by
  rw [value22, value24, value26, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (117 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(113 : Vertex), (119 : Vertex)] := by decide
  have hg := other_cover q (117 : Vertex) (101 : Vertex) [(113 : Vertex), (119 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 10 = false ∨ valuation q 16 = false ∨ valuation q 26 = false := by
  rw [value10, value16, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (118 : Vertex) (54 : Vertex) (102 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 143 = true ∨ valuation q 10 = true ∨ valuation q 16 = true ∨ valuation q 74 = true := by
  rw [value10, value16, value25, value74, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(54 : Vertex), (102 : Vertex), (374 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (119 : Vertex) [(54 : Vertex), (102 : Vertex), (374 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value23, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (119 : Vertex) (115 : Vertex) (117 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 145 = true ∨ valuation q 17 = true := by
  rw [value17, value27, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (120 : Vertex) w → w ∈ region → w ≠ (121 : Vertex) → w ∈ [(104 : Vertex)] := by decide
  have hg := other_cover q (120 : Vertex) (121 : Vertex) [(104 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 22 = true ∨ valuation q 29 = true := by
  rw [value22, value28, value29, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(113 : Vertex), (123 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (120 : Vertex) [(113 : Vertex), (123 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 146 = true ∨ valuation q 22 = true ∨ valuation q 27 = true := by
  rw [value22, value27, value28, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (121 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(113 : Vertex), (120 : Vertex)] := by decide
  have hg := other_cover q (121 : Vertex) (123 : Vertex) [(113 : Vertex), (120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 28 = false := by
  rw [value19, value23, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (123 : Vertex) (107 : Vertex) (115 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 147 = true ∨ valuation q 19 = true ∨ valuation q 28 = true := by
  rw [value19, value28, value29, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(107 : Vertex), (121 : Vertex)] := by decide
  have hg := other_cover q (123 : Vertex) (115 : Vertex) [(107 : Vertex), (121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 39 = false := by
  rw [value30, value31, value34, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (227 : Vertex) (233 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 31 = false ∨ valuation q 39 = false := by
  rw [value31, value39, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (225 : Vertex) (227 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 34 = true ∨ valuation q 39 = true := by
  rw [value30, value34, value39, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(233 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (227 : Vertex) [(233 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 148 = true ∨ valuation q 31 = true ∨ valuation q 39 = true := by
  rw [value30, value31, value39, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(227 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (233 : Vertex) [(227 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 33 = true ∨ valuation q 98 = true := by
  rw [value31, value33, value98, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(231 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (225 : Vertex) [(231 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 30 = true ∨ valuation q 98 = true := by
  rw [value30, value31, value98, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(225 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (231 : Vertex) [(225 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 149 = true ∨ valuation q 30 = true ∨ valuation q 33 = true := by
  rw [value30, value31, value33, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(225 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (483 : Vertex) [(225 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E104.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112104
