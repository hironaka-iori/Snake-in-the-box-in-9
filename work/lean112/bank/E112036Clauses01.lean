import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 10 = false ∨ valuation q 15 = false := by
  rw [value1, value8, value10, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (46 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 136 = true ∨ valuation q 1 = true ∨ valuation q 6 = true ∨ valuation q 15 = true := by
  rw [value1, value6, value8, value15, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(34 : Vertex), (40 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (46 : Vertex) [(34 : Vertex), (40 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 137 = true ∨ valuation q 6 = true ∨ valuation q 10 = true := by
  rw [value6, value9, value10, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (36 : Vertex) [(40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 137 = true ∨ valuation q 3 = true ∨ valuation q 10 = true := by
  rw [value3, value9, value10, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(36 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (40 : Vertex) [(36 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 137 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value9, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(36 : Vertex), (40 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (46 : Vertex) [(36 : Vertex), (40 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 17 = false := by
  rw [value8, value9, value10, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (42 : Vertex) (44 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 138 = true ∨ valuation q 8 = true ∨ valuation q 17 = true := by
  rw [value8, value10, value17, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (44 : Vertex) → w ∈ [(42 : Vertex), (62 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (44 : Vertex) [(42 : Vertex), (62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 139 = true ∨ valuation q 12 = true ∨ valuation q 81 = true := by
  rw [value11, value12, value81, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(53 : Vertex), (308 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (36 : Vertex) [(53 : Vertex), (308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 139 = true ∨ valuation q 3 = true ∨ valuation q 12 = true := by
  rw [value3, value11, value12, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(36 : Vertex), (53 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (308 : Vertex) [(36 : Vertex), (53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 13 = false := by
  rw [value4, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (37 : Vertex) (52 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 140 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value4, value11, value12, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(37 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (55 : Vertex) [(37 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 5 = false ∨ valuation q 12 = false ∨ valuation q 18 = false := by
  rw [value5, value12, value13, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (39 : Vertex) (53 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 141 = true ∨ valuation q 12 = true ∨ valuation q 18 = true := by
  rw [value12, value13, value18, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(53 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (39 : Vertex) [(53 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 141 = true ∨ valuation q 5 = true ∨ valuation q 18 = true := by
  rw [value5, value13, value18, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(39 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(39 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 141 = true ∨ valuation q 5 = true ∨ valuation q 12 = true := by
  rw [value5, value12, value13, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(39 : Vertex), (53 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (63 : Vertex) [(39 : Vertex), (53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 16 = true := by
  rw [value14, value16, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(59 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (41 : Vertex) [(59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 7 = true := by
  rw [value7, value14, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(41 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (59 : Vertex) [(41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value8, value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (59 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 27 = false := by
  rw [value8, value15, value16, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (59 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 83 = false := by
  rw [value8, value15, value16, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (59 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 83 = false := by
  rw [value8, value15, value17, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (62 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 83 = false := by
  rw [value8, value15, value27, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (122 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 27 = false := by
  rw [value15, value16, value17, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (59 : Vertex) (62 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 83 = false := by
  rw [value15, value16, value17, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (59 : Vertex) (62 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 83 = false := by
  rw [value15, value16, value27, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (59 : Vertex) (122 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 18 = false := by
  rw [value14, value15, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (59 : Vertex) (57 : Vertex) (58 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value16, value18, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(58 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (57 : Vertex) [(58 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 14 = true ∨ valuation q 18 = true := by
  rw [value14, value16, value18, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(57 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (58 : Vertex) [(57 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 14 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value16, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(57 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (63 : Vertex) [(57 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 30 = false := by
  rw [value10, value15, value17, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (58 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value13, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (59 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 50 = false := by
  rw [value13, value16, value18, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (59 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E036.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112036
