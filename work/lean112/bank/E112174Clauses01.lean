import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 115 = true := by
  rw [value11, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (84 : Vertex) (85 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 12 = true := by
  rw [value12, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (85 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 13 = true := by
  rw [value9, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex), (84 : Vertex), (87 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (85 : Vertex) [(69 : Vertex), (84 : Vertex), (87 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 116 = true ∨ valuation q 9 = true ∨ valuation q 11 = true := by
  rw [value9, value11, value12, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (87 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 117 = true ∨ valuation q 16 = true := by
  rw [value13, value16, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 117 = true ∨ valuation q 12 = true := by
  rw [value12, value13, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (95 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 14 = true := by
  rw [value14, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (89 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = true := by
  rw [value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ∈ [(91 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (89 : Vertex) [(91 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 118 = true := by
  rw [value14, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (89 : Vertex) (91 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 10 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value10, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (75 : Vertex) (89 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 119 = true ∨ valuation q 14 = true ∨ valuation q 16 = true := by
  rw [value14, value15, value16, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(89 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (75 : Vertex) [(89 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 119 = true ∨ valuation q 10 = true ∨ valuation q 16 = true := by
  rw [value10, value15, value16, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(75 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (89 : Vertex) [(75 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 119 = true ∨ valuation q 10 = true ∨ valuation q 14 = true := by
  rw [value10, value14, value15, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(75 : Vertex), (89 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (95 : Vertex) [(75 : Vertex), (89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 16 = true := by
  rw [value16, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (95 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = true ∨ valuation q 13 = true ∨ valuation q 15 = true := by
  rw [value7, value13, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ∈ [(31 : Vertex), (87 : Vertex), (91 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (95 : Vertex) [(31 : Vertex), (87 : Vertex), (91 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 7 = false ∨ valuation q 13 = false ∨ valuation q 15 = false := by
  rw [value7, value13, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (31 : Vertex) (87 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 120 = true ∨ valuation q 13 = true ∨ valuation q 15 = true := by
  rw [value13, value15, value16, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(87 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (31 : Vertex) [(87 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 120 = true ∨ valuation q 7 = true ∨ valuation q 15 = true := by
  rw [value7, value15, value16, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(31 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (87 : Vertex) [(31 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 120 = true ∨ valuation q 7 = true ∨ valuation q 13 = true := by
  rw [value7, value13, value16, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(31 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (91 : Vertex) [(31 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 8 = false ∨ valuation q 37 = false ∨ valuation q 68 = false := by
  rw [value8, value17, value37, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (67 : Vertex) (227 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 121 = true ∨ valuation q 8 = true ∨ valuation q 37 = true := by
  rw [value8, value17, value37, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(67 : Vertex), (227 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (355 : Vertex) [(67 : Vertex), (227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 18 = true := by
  rw [value18, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (160 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 26 = false := by
  rw [value18, value19, value20, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 122 = true ∨ valuation q 20 = true ∨ valuation q 26 = true := by
  rw [value18, value20, value26, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(162 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(162 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 122 = true ∨ valuation q 19 = true ∨ valuation q 26 = true := by
  rw [value18, value19, value26, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (162 : Vertex) [(161 : Vertex), (176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 122 = true ∨ valuation q 19 = true ∨ valuation q 20 = true := by
  rw [value18, value19, value20, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(161 : Vertex), (162 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (176 : Vertex) [(161 : Vertex), (162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value18, value19, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (163 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value19, value21, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (163 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value18, value20, value21, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 36 = false := by
  rw [value18, value20, value21, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (163 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value18, value20, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 124 = true ∨ valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 28 = true := by
  rw [value18, value20, value21, value28, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (226 : Vertex) [(160 : Vertex), (163 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E174.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112174
