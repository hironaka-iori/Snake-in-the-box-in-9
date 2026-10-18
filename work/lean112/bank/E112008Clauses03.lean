import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 51 = false := by
  rw [value13, value17, value18, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (62 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 51 = true := by
  rw [value13, value17, value18, value51, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (47 : Vertex) → w ∈ [(55 : Vertex), (62 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (47 : Vertex) [(55 : Vertex), (62 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 8 = true ∨ valuation q 13 = true ∨ valuation q 51 = true := by
  rw [value8, value13, value18, value51, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(47 : Vertex), (55 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (62 : Vertex) [(47 : Vertex), (55 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 2 = false ∨ valuation q 23 = false ∨ valuation q 52 = false := by
  rw [value2, value19, value23, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (98 : Vertex) (34 : Vertex) (106 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 23 = true ∨ valuation q 52 = true := by
  rw [value19, value23, value52, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (34 : Vertex) → w ∈ [(106 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (34 : Vertex) [(106 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 2 = true ∨ valuation q 52 = true := by
  rw [value2, value19, value52, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(34 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (106 : Vertex) [(34 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 2 = true ∨ valuation q 23 = true := by
  rw [value2, value19, value23, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (98 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(34 : Vertex), (106 : Vertex)] := by decide
  have hg := other_cover q (98 : Vertex) (226 : Vertex) [(34 : Vertex), (106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 144 = true ∨ valuation q 4 = true ∨ valuation q 55 = true := by
  rw [value4, value20, value55, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(39 : Vertex), (231 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (119 : Vertex) [(39 : Vertex), (231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 23 = true := by
  rw [value21, value23, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(106 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (105 : Vertex) [(106 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 22 = true := by
  rw [value21, value22, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(105 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (106 : Vertex) [(105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 5 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value5, value21, value22, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (104 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 5 = false ∨ valuation q 21 = false ∨ valuation q 56 = false := by
  rw [value5, value21, value22, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (104 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 5 = false ∨ valuation q 28 = false ∨ valuation q 56 = false := by
  rw [value5, value22, value28, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (121 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 56 = false := by
  rw [value21, value22, value28, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (104 : Vertex) (121 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 5 = true ∨ valuation q 21 = true ∨ valuation q 56 = true := by
  rw [value5, value21, value22, value56, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (121 : Vertex) → w ∈ [(41 : Vertex), (104 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (121 : Vertex) [(41 : Vertex), (104 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 146 = true ∨ valuation q 5 = true ∨ valuation q 21 = true ∨ valuation q 28 = true := by
  rw [value5, value21, value22, value28, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(41 : Vertex), (104 : Vertex), (121 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (233 : Vertex) [(41 : Vertex), (104 : Vertex), (121 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 21 = false := by
  rw [value6, value19, value21, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 29 = false := by
  rw [value6, value19, value23, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 57 = false := by
  rw [value6, value19, value23, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (98 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 29 = false := by
  rw [value6, value21, value23, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (104 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 21 = false ∨ valuation q 57 = false := by
  rw [value6, value21, value23, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (104 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 6 = false ∨ valuation q 29 = false ∨ valuation q 57 = false := by
  rw [value6, value23, value29, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (42 : Vertex) (122 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 29 = false := by
  rw [value19, value21, value23, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (98 : Vertex) (104 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 57 = false := by
  rw [value19, value21, value23, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (98 : Vertex) (104 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 29 = false ∨ valuation q 57 = false := by
  rw [value19, value23, value29, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (98 : Vertex) (122 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 57 = false := by
  rw [value21, value23, value29, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (106 : Vertex) (104 : Vertex) (122 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 29 = true ∨ valuation q 57 = true := by
  rw [value19, value21, value23, value24, value29, value57, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(98 : Vertex), (104 : Vertex), (110 : Vertex), (122 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (42 : Vertex) [(98 : Vertex), (104 : Vertex), (110 : Vertex), (122 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 6 = true ∨ valuation q 19 = true ∨ valuation q 24 = true ∨ valuation q 29 = true ∨ valuation q 57 = true := by
  rw [value6, value19, value23, value24, value29, value57, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(42 : Vertex), (98 : Vertex), (110 : Vertex), (122 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (104 : Vertex) [(42 : Vertex), (98 : Vertex), (110 : Vertex), (122 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 147 = true ∨ valuation q 6 = true ∨ valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 57 = true := by
  rw [value6, value19, value21, value23, value24, value57, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(42 : Vertex), (98 : Vertex), (104 : Vertex), (110 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (122 : Vertex) [(42 : Vertex), (98 : Vertex), (104 : Vertex), (110 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true := by
  rw [value24, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (110 : Vertex) (106 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 31 = true := by
  rw [value25, value31, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (117 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (117 : Vertex) (119 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = true := by
  rw [value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ∈ [(119 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (118 : Vertex) [(119 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E008.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112008
