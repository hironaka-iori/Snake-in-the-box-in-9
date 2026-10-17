import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 125 = true ∨ valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 16 = true ∨ valuation q 47 = true ∨ valuation q 80 = true := by
  rw [value5, value6, value9, value16, value47, value80, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (40 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(41 : Vertex), (44 : Vertex), (56 : Vertex), (168 : Vertex), (296 : Vertex)] := by decide
  have hg := other_cover q (40 : Vertex) (42 : Vertex) [(41 : Vertex), (44 : Vertex), (56 : Vertex), (168 : Vertex), (296 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 25 = false := by
  rw [value6, value8, value17, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (43 : Vertex) (57 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 8 = true ∨ valuation q 17 = true ∨ valuation q 25 = true := by
  rw [value6, value8, value17, value25, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(43 : Vertex), (57 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (40 : Vertex) [(43 : Vertex), (57 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 5 = true ∨ valuation q 17 = true ∨ valuation q 25 = true := by
  rw [value5, value6, value17, value25, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(40 : Vertex), (57 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (43 : Vertex) [(40 : Vertex), (57 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 25 = true := by
  rw [value5, value6, value8, value25, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(40 : Vertex), (43 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (57 : Vertex) [(40 : Vertex), (43 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 126 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 17 = true := by
  rw [value5, value6, value8, value17, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(40 : Vertex), (43 : Vertex), (57 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (105 : Vertex) [(40 : Vertex), (43 : Vertex), (57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 8 = false := by
  rw [value1, value5, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (40 : Vertex) (43 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 10 = false := by
  rw [value1, value5, value7, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (40 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 1 = false ∨ valuation q 8 = false ∨ valuation q 10 = false := by
  rw [value1, value7, value8, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (42 : Vertex) (34 : Vertex) (43 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 127 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 10 = true := by
  rw [value5, value7, value8, value10, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(40 : Vertex), (43 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (34 : Vertex) [(40 : Vertex), (43 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 127 = true ∨ valuation q 1 = true ∨ valuation q 8 = true ∨ valuation q 10 = true := by
  rw [value1, value7, value8, value10, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(34 : Vertex), (43 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (40 : Vertex) [(34 : Vertex), (43 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 127 = true ∨ valuation q 1 = true ∨ valuation q 5 = true ∨ valuation q 10 = true := by
  rw [value1, value5, value7, value10, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(34 : Vertex), (40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (43 : Vertex) [(34 : Vertex), (40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 127 = true ∨ valuation q 1 = true ∨ valuation q 5 = true ∨ valuation q 8 = true := by
  rw [value1, value5, value7, value8, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (42 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(34 : Vertex), (40 : Vertex), (43 : Vertex)] := by decide
  have hg := other_cover q (42 : Vertex) (46 : Vertex) [(34 : Vertex), (40 : Vertex), (43 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 26 = false := by
  rw [value6, value7, value8, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (41 : Vertex) (42 : Vertex) (107 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 128 = true ∨ valuation q 7 = true ∨ valuation q 26 = true := by
  rw [value7, value8, value26, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (43 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(42 : Vertex), (107 : Vertex)] := by decide
  have hg := other_cover q (43 : Vertex) (41 : Vertex) [(42 : Vertex), (107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 128 = true ∨ valuation q 6 = true ∨ valuation q 26 = true := by
  rw [value6, value8, value26, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (43 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(41 : Vertex), (107 : Vertex)] := by decide
  have hg := other_cover q (43 : Vertex) (42 : Vertex) [(41 : Vertex), (107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 10 = false := by
  rw [value2, value5, value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (44 : Vertex) (36 : Vertex) (40 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 27 = false := by
  rw [value2, value5, value9, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (44 : Vertex) (36 : Vertex) (40 : Vertex) (108 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 10 = false ∨ valuation q 27 = false := by
  rw [value2, value9, value10, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (44 : Vertex) (36 : Vertex) (46 : Vertex) (108 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 27 = false := by
  rw [value5, value9, value10, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (44 : Vertex) (40 : Vertex) (46 : Vertex) (108 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 129 = true ∨ valuation q 5 = true ∨ valuation q 10 = true ∨ valuation q 27 = true ∨ valuation q 81 = true := by
  rw [value5, value9, value10, value27, value81, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(40 : Vertex), (46 : Vertex), (108 : Vertex), (300 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (36 : Vertex) [(40 : Vertex), (46 : Vertex), (108 : Vertex), (300 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 9 = false := by
  rw [value4, value7, value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (38 : Vertex) (42 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 4 = false ∨ valuation q 7 = false ∨ valuation q 18 = false := by
  rw [value4, value7, value10, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (38 : Vertex) (42 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 18 = false := by
  rw [value4, value9, value10, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (38 : Vertex) (44 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 18 = false := by
  rw [value7, value9, value10, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (46 : Vertex) (42 : Vertex) (44 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 30 = false := by
  rw [value11, value12, value16, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (49 : Vertex) (56 : Vertex) (112 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 50 = false := by
  rw [value11, value12, value16, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (49 : Vertex) (56 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 50 = false := by
  rw [value11, value16, value30, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (56 : Vertex) (112 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 30 = true ∨ valuation q 50 = true := by
  rw [value11, value12, value30, value50, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (48 : Vertex) w → w ∈ region → w ≠ (56 : Vertex) → w ∈ [(49 : Vertex), (112 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (48 : Vertex) (56 : Vertex) [(49 : Vertex), (112 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value11, value12, value14, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (48 : Vertex) (53 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 132 = true ∨ valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 17 = true := by
  rw [value11, value12, value14, value17, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (51 : Vertex) → w ∈ [(48 : Vertex), (53 : Vertex), (57 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (51 : Vertex) [(48 : Vertex), (53 : Vertex), (57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 132 = true ∨ valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 17 = true := by
  rw [value11, value12, value13, value17, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (49 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(48 : Vertex), (51 : Vertex), (57 : Vertex)] := by decide
  have hg := other_cover q (49 : Vertex) (53 : Vertex) [(48 : Vertex), (51 : Vertex), (57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E040.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112040
