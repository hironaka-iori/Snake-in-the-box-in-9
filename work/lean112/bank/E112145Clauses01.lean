import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 14 = false := by
  rw [value8, value10, value11, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (32 : Vertex) (38 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 11 = false ∨ valuation q 16 = false := by
  rw [value8, value10, value11, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (32 : Vertex) (38 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value8, value10, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (32 : Vertex) (44 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value10, value11, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (38 : Vertex) (44 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 114 = true ∨ valuation q 8 = true ∨ valuation q 11 = true ∨ valuation q 16 = true := by
  rw [value8, value10, value11, value16, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (44 : Vertex) → w ∈ [(32 : Vertex), (38 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (44 : Vertex) [(32 : Vertex), (38 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 12 = false := by
  rw [value3, value10, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (39 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 15 = false := by
  rw [value3, value10, value11, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 22 = false := by
  rw [value3, value10, value11, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (36 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value3, value11, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (39 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 3 = false ∨ valuation q 15 = false ∨ valuation q 22 = false := by
  rw [value3, value11, value15, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (6 : Vertex) (46 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 22 = false := by
  rw [value11, value12, value15, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (39 : Vertex) (46 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 18 = false ∨ valuation q 23 = false := by
  rw [value11, value12, value18, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (39 : Vertex) (38 : Vertex) (55 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 116 = true ∨ valuation q 11 = true ∨ valuation q 18 = true := by
  rw [value11, value12, value18, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(38 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (103 : Vertex) [(38 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value9, value13, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (46 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value15, value19, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (42 : Vertex) (46 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 117 = true ∨ valuation q 9 = true ∨ valuation q 15 = true := by
  rw [value9, value13, value15, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(34 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (58 : Vertex) [(34 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 10 = true ∨ valuation q 15 = true := by
  rw [value10, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ∈ [(36 : Vertex), (46 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (44 : Vertex) [(36 : Vertex), (46 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 118 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(46 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (36 : Vertex) [(46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 118 = true ∨ valuation q 10 = true := by
  rw [value10, value14, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(36 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (46 : Vertex) [(36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value11, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (38 : Vertex) (42 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 119 = true ∨ valuation q 11 = true ∨ valuation q 14 = true := by
  rw [value11, value14, value15, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(38 : Vertex), (44 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (42 : Vertex) [(38 : Vertex), (44 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 119 = true ∨ valuation q 11 = true ∨ valuation q 13 = true := by
  rw [value11, value13, value15, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (44 : Vertex) → w ∈ [(38 : Vertex), (42 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (44 : Vertex) [(38 : Vertex), (42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 10 = true ∨ valuation q 17 = true := by
  rw [value10, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ∈ [(36 : Vertex), (53 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (52 : Vertex) [(36 : Vertex), (53 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 10 = false ∨ valuation q 17 = false := by
  rw [value10, value17, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (52 : Vertex) (36 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 120 = true ∨ valuation q 17 = true := by
  rw [value16, value17, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (36 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 120 = true ∨ valuation q 10 = true := by
  rw [value10, value16, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(36 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (53 : Vertex) [(36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 121 = true ∨ valuation q 18 = true := by
  rw [value17, value18, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (52 : Vertex) → w ∈ [(55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (52 : Vertex) [(55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 121 = true ∨ valuation q 16 = true := by
  rw [value16, value17, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(52 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (55 : Vertex) [(52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 18 = true := by
  rw [value18, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (55 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 12 = true ∨ valuation q 17 = true := by
  rw [value12, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ∈ [(39 : Vertex), (53 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (55 : Vertex) [(39 : Vertex), (53 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 122 = true ∨ valuation q 17 = true := by
  rw [value17, value18, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (39 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 122 = true ∨ valuation q 12 = true := by
  rw [value12, value18, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(39 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(39 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E145.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112145
