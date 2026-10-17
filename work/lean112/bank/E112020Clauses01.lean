import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 29 = false := by
  rw [value8, value10, value12, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (49 : Vertex) (59 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 47 = false := by
  rw [value8, value10, value12, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (49 : Vertex) (59 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = false ∨ valuation q 29 = false ∨ valuation q 47 = false := by
  rw [value8, value10, value29, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (49 : Vertex) (121 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 29 = false ∨ valuation q 47 = false := by
  rw [value10, value12, value29, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (59 : Vertex) (121 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 8 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 29 = true ∨ valuation q 47 = true := by
  rw [value8, value10, value12, value13, value29, value47, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(49 : Vertex), (59 : Vertex), (61 : Vertex), (121 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (41 : Vertex) [(49 : Vertex), (59 : Vertex), (61 : Vertex), (121 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 13 = true ∨ valuation q 29 = true ∨ valuation q 47 = true := by
  rw [value5, value8, value10, value13, value29, value47, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(41 : Vertex), (49 : Vertex), (61 : Vertex), (121 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (59 : Vertex) [(41 : Vertex), (49 : Vertex), (61 : Vertex), (121 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 47 = true := by
  rw [value5, value8, value10, value12, value13, value47, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (121 : Vertex) → w ∈ [(41 : Vertex), (49 : Vertex), (59 : Vertex), (61 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (121 : Vertex) [(41 : Vertex), (49 : Vertex), (59 : Vertex), (61 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 134 = true ∨ valuation q 5 = true ∨ valuation q 8 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 29 = true := by
  rw [value5, value8, value10, value12, value13, value29, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(41 : Vertex), (49 : Vertex), (59 : Vertex), (61 : Vertex), (121 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (185 : Vertex) [(41 : Vertex), (49 : Vertex), (59 : Vertex), (61 : Vertex), (121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 30 = false := by
  rw [value6, value11, value12, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (59 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 48 = false := by
  rw [value6, value11, value12, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (59 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 6 = false ∨ valuation q 30 = false ∨ valuation q 48 = false := by
  rw [value6, value11, value30, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (42 : Vertex) (122 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 30 = false ∨ valuation q 48 = false := by
  rw [value11, value12, value30, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (59 : Vertex) (122 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 12 = true ∨ valuation q 30 = true ∨ valuation q 48 = true := by
  rw [value11, value12, value30, value48, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(59 : Vertex), (122 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (58 : Vertex) (42 : Vertex) [(59 : Vertex), (122 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 135 = true ∨ valuation q 6 = true ∨ valuation q 12 = true ∨ valuation q 48 = true := by
  rw [value6, value11, value12, value48, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(42 : Vertex), (59 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (58 : Vertex) (122 : Vertex) [(42 : Vertex), (59 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 11 = true := by
  rw [value11, value12, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(58 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (57 : Vertex) [(58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 136 = true ∨ valuation q 10 = true := by
  rw [value10, value12, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(57 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (58 : Vertex) [(57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 137 = true := by
  rw [value13, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (61 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (61 : Vertex) (57 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 24 = false := by
  rw [value14, value15, value16, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (97 : Vertex) (98 : Vertex) (112 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 24 = true := by
  rw [value14, value15, value24, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (98 : Vertex) → w ∈ [(97 : Vertex), (112 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (98 : Vertex) [(97 : Vertex), (112 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 138 = true ∨ valuation q 15 = true ∨ valuation q 16 = true := by
  rw [value14, value15, value16, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (112 : Vertex) → w ∈ [(97 : Vertex), (98 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (112 : Vertex) [(97 : Vertex), (98 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 51 = false := by
  rw [value14, value15, value17, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (96 : Vertex) (99 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 71 = false := by
  rw [value14, value15, value17, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (96 : Vertex) (99 : Vertex) (353 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value14, value15, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (96 : Vertex) (105 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 25 = false := by
  rw [value15, value17, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (99 : Vertex) (105 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 51 = false := by
  rw [value15, value17, value25, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (99 : Vertex) (113 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 71 = false := by
  rw [value15, value17, value25, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (99 : Vertex) (113 : Vertex) (353 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 17 = true ∨ valuation q 26 = true := by
  rw [value16, value17, value26, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(99 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (96 : Vertex) [(99 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 14 = true ∨ valuation q 26 = true := by
  rw [value14, value16, value26, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(96 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (99 : Vertex) [(96 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 140 = true ∨ valuation q 14 = true ∨ valuation q 17 = true := by
  rw [value14, value16, value17, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(96 : Vertex), (99 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (114 : Vertex) [(96 : Vertex), (99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value15, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (98 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 27 = false := by
  rw [value15, value16, value17, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (98 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 27 = false := by
  rw [value15, value17, value18, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (103 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E020.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112020
