import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 50 = true := by
  rw [value16, value17, value18, value50, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(59 : Vertex), (62 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (55 : Vertex) [(59 : Vertex), (62 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 22 = true := by
  rw [value19, value22, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(105 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (99 : Vertex) [(105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 87 = false := by
  rw [value2, value19, value20, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (35 : Vertex) (97 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 2 = false ∨ valuation q 21 = false ∨ valuation q 87 = false := by
  rw [value2, value20, value21, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (35 : Vertex) (103 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 2 = false ∨ valuation q 52 = false ∨ valuation q 87 = false := by
  rw [value2, value20, value52, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (35 : Vertex) (227 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 87 = false := by
  rw [value19, value20, value21, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (103 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 52 = false ∨ valuation q 87 = false := by
  rw [value19, value20, value52, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (97 : Vertex) (227 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 52 = false ∨ valuation q 87 = false := by
  rw [value20, value21, value52, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (103 : Vertex) (227 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 20 = false ∨ valuation q 24 = false := by
  rw [value5, value20, value21, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (103 : Vertex) (39 : Vertex) (99 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 149 = true ∨ valuation q 5 = true ∨ valuation q 24 = true := by
  rw [value5, value21, value24, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(39 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (99 : Vertex) [(39 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 19 = false ∨ valuation q 23 = false := by
  rw [value7, value19, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 19 = false ∨ valuation q 56 = false := by
  rw [value7, value19, value22, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 56 = false := by
  rw [value7, value22, value23, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (109 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 56 = false := by
  rw [value19, value22, value23, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (109 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 7 = true ∨ valuation q 19 = true ∨ valuation q 56 = true := by
  rw [value7, value19, value22, value56, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(41 : Vertex), (97 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (109 : Vertex) [(41 : Vertex), (97 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 29 = false := by
  rw [value22, value23, value24, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (105 : Vertex) (111 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 151 = true ∨ valuation q 24 = true ∨ valuation q 29 = true := by
  rw [value23, value24, value29, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(111 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (105 : Vertex) [(111 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 151 = true ∨ valuation q 22 = true ∨ valuation q 29 = true := by
  rw [value22, value23, value29, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(105 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (111 : Vertex) [(105 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 151 = true ∨ valuation q 22 = true ∨ valuation q 24 = true := by
  rw [value22, value23, value24, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(105 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (125 : Vertex) [(105 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 152 = true ∨ valuation q 23 = true := by
  rw [value23, value24, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (103 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 152 = true ∨ valuation q 21 = true := by
  rw [value21, value24, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(103 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (109 : Vertex) [(103 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 153 = true := by
  rw [value25, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (115 : Vertex) (99 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 154 = true := by
  rw [value26, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (118 : Vertex) (126 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 15 = false ∨ valuation q 30 = false ∨ valuation q 66 = false := by
  rw [value15, value27, value30, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (122 : Vertex) (58 : Vertex) (126 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 155 = true ∨ valuation q 15 = true ∨ valuation q 66 = true := by
  rw [value15, value27, value66, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(58 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (126 : Vertex) [(58 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 30 = true := by
  rw [value28, value30, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 29 = true := by
  rw [value28, value29, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 157 = true ∨ valuation q 28 = true := by
  rw [value28, value29, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(124 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (109 : Vertex) [(124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 157 = true ∨ valuation q 23 = true := by
  rw [value23, value29, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(109 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (124 : Vertex) [(109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value17, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (62 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 26 = true ∨ valuation q 27 = true ∨ valuation q 28 = true := by
  rw [value26, value27, value28, value30, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(118 : Vertex), (122 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (62 : Vertex) [(118 : Vertex), (122 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 17 = true ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value17, value26, value28, value30, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(62 : Vertex), (118 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (122 : Vertex) [(62 : Vertex), (118 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E036.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112036
