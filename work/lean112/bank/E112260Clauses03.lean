import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 48 = false := by
  rw [value10, value11, value15, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (89 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 89 = false := by
  rw [value10, value11, value15, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (89 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 28 = false ∨ valuation q 48 = false := by
  rw [value10, value11, value28, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (113 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 28 = false ∨ valuation q 89 = false := by
  rw [value10, value11, value28, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (113 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = false ∨ valuation q 48 = false ∨ valuation q 89 = false := by
  rw [value10, value11, value48, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (80 : Vertex) (209 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 28 = false := by
  rw [value11, value12, value15, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (83 : Vertex) (89 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 48 = false := by
  rw [value11, value12, value15, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (83 : Vertex) (89 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 89 = false := by
  rw [value11, value12, value15, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (83 : Vertex) (89 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 48 = false := by
  rw [value11, value12, value28, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (83 : Vertex) (113 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 89 = false := by
  rw [value11, value12, value28, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (83 : Vertex) (113 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 48 = false ∨ valuation q 89 = false := by
  rw [value11, value12, value48, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (83 : Vertex) (209 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 28 = false ∨ valuation q 48 = false := by
  rw [value11, value15, value28, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (89 : Vertex) (113 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 28 = false ∨ valuation q 89 = false := by
  rw [value11, value15, value28, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (89 : Vertex) (113 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 89 = false := by
  rw [value11, value15, value48, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (89 : Vertex) (209 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 28 = false ∨ valuation q 48 = false ∨ valuation q 89 = false := by
  rw [value11, value28, value48, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (113 : Vertex) (209 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 48 = true ∨ valuation q 89 = true := by
  rw [value10, value11, value12, value15, value28, value48, value89, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(80 : Vertex), (83 : Vertex), (89 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (65 : Vertex) [(80 : Vertex), (83 : Vertex), (89 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 1 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 48 = true ∨ valuation q 89 = true := by
  rw [value1, value11, value12, value15, value28, value48, value89, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(65 : Vertex), (83 : Vertex), (89 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (80 : Vertex) [(65 : Vertex), (83 : Vertex), (89 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 1 = true ∨ valuation q 10 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 48 = true ∨ valuation q 89 = true := by
  rw [value1, value10, value11, value15, value28, value48, value89, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(65 : Vertex), (80 : Vertex), (89 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (83 : Vertex) [(65 : Vertex), (80 : Vertex), (89 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 1 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 28 = true ∨ valuation q 48 = true ∨ valuation q 89 = true := by
  rw [value1, value10, value11, value12, value28, value48, value89, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(65 : Vertex), (80 : Vertex), (83 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (89 : Vertex) [(65 : Vertex), (80 : Vertex), (83 : Vertex), (113 : Vertex), (209 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 1 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 48 = true ∨ valuation q 89 = true := by
  rw [value1, value10, value11, value12, value15, value48, value89, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(65 : Vertex), (80 : Vertex), (83 : Vertex), (89 : Vertex), (209 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (113 : Vertex) [(65 : Vertex), (80 : Vertex), (83 : Vertex), (89 : Vertex), (209 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 138 = true ∨ valuation q 1 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 89 = true := by
  rw [value1, value10, value11, value12, value15, value28, value89, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(65 : Vertex), (80 : Vertex), (83 : Vertex), (89 : Vertex), (113 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (209 : Vertex) [(65 : Vertex), (80 : Vertex), (83 : Vertex), (89 : Vertex), (113 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 12 = true := by
  rw [value12, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (83 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 29 = true := by
  rw [value11, value12, value14, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ∈ [(81 : Vertex), (87 : Vertex), (115 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (83 : Vertex) [(81 : Vertex), (87 : Vertex), (115 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 29 = false := by
  rw [value11, value12, value14, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (81 : Vertex) (87 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 14 = true ∨ valuation q 29 = true := by
  rw [value12, value14, value29, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(87 : Vertex), (115 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (81 : Vertex) [(87 : Vertex), (115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 11 = true ∨ valuation q 29 = true := by
  rw [value11, value12, value29, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(81 : Vertex), (115 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (87 : Vertex) [(81 : Vertex), (115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 139 = true ∨ valuation q 11 = true ∨ valuation q 14 = true := by
  rw [value11, value12, value14, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(81 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (115 : Vertex) [(81 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 10 = false ∨ valuation q 30 = false ∨ valuation q 50 = false := by
  rw [value10, value13, value30, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (80 : Vertex) (116 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 140 = true ∨ valuation q 30 = true ∨ valuation q 50 = true := by
  rw [value13, value30, value50, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(116 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(116 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 140 = true ∨ valuation q 10 = true ∨ valuation q 50 = true := by
  rw [value10, value13, value50, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(80 : Vertex), (212 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (116 : Vertex) [(80 : Vertex), (212 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 140 = true ∨ valuation q 10 = true ∨ valuation q 30 = true := by
  rw [value10, value13, value30, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(80 : Vertex), (116 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (212 : Vertex) [(80 : Vertex), (116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 5 = false ∨ valuation q 12 = false ∨ valuation q 51 = false := by
  rw [value5, value12, value14, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (71 : Vertex) (83 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E260.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112260
