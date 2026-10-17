import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 9 = false := by
  rw [value1, value2, value3, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (36 : Vertex) (37 : Vertex) (38 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 2 = false ∨ valuation q 9 = false := by
  rw [value2, value9, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (36 : Vertex) (37 : Vertex) (52 : Vertex) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 125 = true ∨ valuation q 3 = true ∨ valuation q 9 = true := by
  rw [value1, value3, value9, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (36 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(38 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (36 : Vertex) (37 : Vertex) [(38 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 1 = true := by
  rw [value1, value2]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (37 : Vertex) w → w ∈ region → w ∈ [(36 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (37 : Vertex) [(36 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 2 = true := by
  rw [value2]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 127 = true ∨ valuation q 7 = true := by
  rw [value3, value7, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (38 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(46 : Vertex)] := by decide
  have hg := other_cover q (38 : Vertex) (36 : Vertex) [(46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(42 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (41 : Vertex) [(42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 128 = true ∨ valuation q 5 = true := by
  rw [value4, value5, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(41 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (42 : Vertex) [(41 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 10 = false ∨ valuation q 19 = false := by
  rw [value4, value5, value10, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (57 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 10 = true ∨ valuation q 19 = true := by
  rw [value5, value10, value19, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(57 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (40 : Vertex) [(57 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 4 = true ∨ valuation q 19 = true := by
  rw [value4, value5, value19, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(40 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (57 : Vertex) [(40 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 129 = true ∨ valuation q 4 = true ∨ valuation q 10 = true := by
  rw [value4, value5, value10, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(40 : Vertex), (57 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (105 : Vertex) [(40 : Vertex), (57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 11 = false := by
  rw [value4, value6, value7, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (40 : Vertex) (46 : Vertex) (58 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 7 = true ∨ valuation q 11 = true := by
  rw [value6, value7, value11, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(46 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (40 : Vertex) [(46 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 11 = true := by
  rw [value4, value6, value11, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(40 : Vertex), (58 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (46 : Vertex) [(40 : Vertex), (58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 7 = true := by
  rw [value4, value6, value7, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (58 : Vertex) [(40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 22 = false := by
  rw [value3, value6, value7, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (38 : Vertex) (42 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true ∨ valuation q 6 = true ∨ valuation q 22 = true := by
  rw [value6, value7, value22, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (38 : Vertex) → w ∈ [(42 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (38 : Vertex) [(42 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 131 = true ∨ valuation q 3 = true ∨ valuation q 22 = true := by
  rw [value3, value7, value22, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(38 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (42 : Vertex) [(38 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 43 = false := by
  rw [value8, value10, value25, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (57 : Vertex) (113 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 25 = true ∨ valuation q 43 = true := by
  rw [value8, value25, value43, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(113 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (57 : Vertex) [(113 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 10 = true ∨ valuation q 43 = true := by
  rw [value8, value10, value43, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(57 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (113 : Vertex) [(57 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 132 = true ∨ valuation q 10 = true ∨ valuation q 25 = true := by
  rw [value8, value10, value25, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(57 : Vertex), (113 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (177 : Vertex) [(57 : Vertex), (113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 1 = false ∨ valuation q 28 = false ∨ valuation q 44 = false := by
  rw [value1, value9, value28, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (52 : Vertex) (36 : Vertex) (116 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 133 = true ∨ valuation q 28 = true ∨ valuation q 44 = true := by
  rw [value9, value28, value44, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(116 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (36 : Vertex) [(116 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 29 = true ∨ valuation q 47 = true := by
  rw [value5, value8, value10, value12, value13, value29, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ∈ [(41 : Vertex), (49 : Vertex), (59 : Vertex), (61 : Vertex), (121 : Vertex), (185 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (57 : Vertex) [(41 : Vertex), (49 : Vertex), (59 : Vertex), (61 : Vertex), (121 : Vertex), (185 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 12 = false := by
  rw [value5, value8, value10, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (49 : Vertex) (59 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 29 = false := by
  rw [value5, value8, value10, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (49 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 47 = false := by
  rw [value5, value8, value10, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (49 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 12 = false ∨ valuation q 29 = false := by
  rw [value5, value10, value12, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (59 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 12 = false ∨ valuation q 47 = false := by
  rw [value5, value10, value12, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (59 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 5 = false ∨ valuation q 29 = false ∨ valuation q 47 = false := by
  rw [value5, value10, value29, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (121 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E020.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112020
