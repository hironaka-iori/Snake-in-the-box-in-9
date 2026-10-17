import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value6, value14, value15, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 14 = false ∨ valuation q 55 = false := by
  rw [value6, value14, value15, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (88 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 6 = false ∨ valuation q 17 = false ∨ valuation q 55 = false := by
  rw [value6, value15, value17, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (91 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 55 = false := by
  rw [value14, value15, value17, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (88 : Vertex) (91 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 55 = true := by
  rw [value14, value15, value17, value55, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(88 : Vertex), (91 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (73 : Vertex) [(88 : Vertex), (91 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 134 = true ∨ valuation q 6 = true ∨ valuation q 17 = true ∨ valuation q 55 = true := by
  rw [value6, value15, value17, value55, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(73 : Vertex), (91 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (88 : Vertex) [(73 : Vertex), (91 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 134 = true ∨ valuation q 6 = true ∨ valuation q 14 = true ∨ valuation q 55 = true := by
  rw [value6, value14, value15, value55, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(73 : Vertex), (88 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (91 : Vertex) [(73 : Vertex), (88 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 134 = true ∨ valuation q 6 = true ∨ valuation q 14 = true ∨ valuation q 17 = true := by
  rw [value6, value14, value15, value17, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(73 : Vertex), (88 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (217 : Vertex) [(73 : Vertex), (88 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 17 = false := by
  rw [value7, value14, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 56 = false := by
  rw [value7, value14, value16, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (88 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 17 = false ∨ valuation q 56 = false := by
  rw [value7, value16, value17, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (91 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 56 = false ∨ valuation q 81 = false := by
  rw [value7, value16, value56, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (74 : Vertex) (218 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 56 = false := by
  rw [value14, value16, value17, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 81 = false := by
  rw [value14, value16, value17, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value15, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (89 : Vertex) (90 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 136 = true ∨ valuation q 16 = true ∨ valuation q 18 = true := by
  rw [value16, value17, value18, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(90 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (89 : Vertex) [(90 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value15, value17, value18, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(89 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (90 : Vertex) [(89 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 136 = true ∨ valuation q 15 = true ∨ valuation q 16 = true := by
  rw [value15, value16, value17, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(89 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (95 : Vertex) [(89 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 13 = false ∨ valuation q 17 = false := by
  rw [value13, value17, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (95 : Vertex) (87 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 137 = true ∨ valuation q 17 = true := by
  rw [value17, value18, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (87 : Vertex) [(91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 137 = true ∨ valuation q 13 = true := by
  rw [value13, value18, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (91 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 26 = true ∨ valuation q 39 = true := by
  rw [value19, value20, value22, value26, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ∈ [(131 : Vertex), (134 : Vertex), (138 : Vertex), (194 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (130 : Vertex) [(131 : Vertex), (134 : Vertex), (138 : Vertex), (194 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value19, value20, value22, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (134 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 39 = false := by
  rw [value19, value20, value22, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (134 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 26 = false ∨ valuation q 39 = false := by
  rw [value19, value20, value26, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 39 = false := by
  rw [value19, value22, value26, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 138 = true ∨ valuation q 22 = true ∨ valuation q 26 = true ∨ valuation q 39 = true := by
  rw [value19, value22, value26, value39, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (131 : Vertex) → w ∈ [(134 : Vertex), (138 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (131 : Vertex) [(134 : Vertex), (138 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 138 = true ∨ valuation q 20 = true ∨ valuation q 26 = true ∨ valuation q 39 = true := by
  rw [value19, value20, value26, value39, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(131 : Vertex), (138 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (134 : Vertex) [(131 : Vertex), (138 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 138 = true ∨ valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 39 = true := by
  rw [value19, value20, value22, value39, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(131 : Vertex), (134 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (138 : Vertex) [(131 : Vertex), (134 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 40 = false := by
  rw [value19, value20, value23, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (131 : Vertex) (130 : Vertex) (135 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 139 = true ∨ valuation q 23 = true ∨ valuation q 40 = true := by
  rw [value20, value23, value40, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(135 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (130 : Vertex) [(135 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 139 = true ∨ valuation q 19 = true ∨ valuation q 40 = true := by
  rw [value19, value20, value40, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (131 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(130 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (131 : Vertex) (135 : Vertex) [(130 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E078.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112078
