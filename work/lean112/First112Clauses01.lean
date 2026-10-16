import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 61 = false := by
  rw [value2, value6, value7, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (35 : Vertex) (42 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 15 = false ∨ valuation q 26 = false := by
  rw [value2, value7, value15, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (35 : Vertex) (59 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 15 = false ∨ valuation q 61 = false := by
  rw [value2, value7, value15, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (35 : Vertex) (59 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 2 = false ∨ valuation q 26 = false ∨ valuation q 61 = false := by
  rw [value2, value7, value26, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (35 : Vertex) (171 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 15 = false ∨ valuation q 26 = false := by
  rw [value6, value7, value15, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (42 : Vertex) (59 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 15 = false ∨ valuation q 61 = false := by
  rw [value6, value7, value15, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (42 : Vertex) (59 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 26 = false ∨ valuation q 61 = false := by
  rw [value6, value7, value26, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (42 : Vertex) (171 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 15 = false ∨ valuation q 26 = false ∨ valuation q 61 = false := by
  rw [value7, value15, value26, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (43 : Vertex) (59 : Vertex) (171 : Vertex) (299 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 129 = true ∨ valuation q 2 = true ∨ valuation q 6 = true ∨ valuation q 15 = true ∨ valuation q 26 = true := by
  rw [value2, value6, value7, value15, value26, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (43 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(35 : Vertex), (42 : Vertex), (59 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (43 : Vertex) (299 : Vertex) [(35 : Vertex), (42 : Vertex), (59 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 130 = true ∨ valuation q 5 = true ∨ valuation q 9 = true := by
  rw [value5, value8, value9, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (36 : Vertex) → w ∈ [(40 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (36 : Vertex) [(40 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 130 = true ∨ valuation q 3 = true ∨ valuation q 9 = true := by
  rw [value3, value8, value9, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(36 : Vertex), (46 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (40 : Vertex) [(36 : Vertex), (46 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 130 = true ∨ valuation q 3 = true ∨ valuation q 5 = true := by
  rw [value3, value5, value8, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(36 : Vertex), (40 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (46 : Vertex) [(36 : Vertex), (40 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 131 = true ∨ valuation q 8 = true := by
  rw [value8, value9, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (42 : Vertex) → w ∈ [(44 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (42 : Vertex) [(44 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 131 = true ∨ valuation q 6 = true := by
  rw [value6, value9, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (46 : Vertex) w → w ∈ region → w ≠ (44 : Vertex) → w ∈ [(42 : Vertex)] := by decide
  have hg := other_cover q (46 : Vertex) (44 : Vertex) [(42 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 32 = false := by
  rw [value3, value10, value11, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (52 : Vertex) (36 : Vertex) (53 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 132 = true ∨ valuation q 3 = true ∨ valuation q 32 = true := by
  rw [value3, value10, value32, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (52 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(36 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (52 : Vertex) (53 : Vertex) [(36 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 4 = false ∨ valuation q 10 = false ∨ valuation q 12 = false := by
  rw [value4, value10, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (37 : Vertex) (52 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 4 = false ∨ valuation q 12 = false := by
  rw [value4, value12, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (53 : Vertex) (37 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 133 = true ∨ valuation q 10 = true ∨ valuation q 12 = true := by
  rw [value10, value11, value12, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(52 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (37 : Vertex) [(52 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 10 = true := by
  rw [value4, value10, value11, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(37 : Vertex), (52 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (55 : Vertex) [(37 : Vertex), (52 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 134 = true ∨ valuation q 16 = true := by
  rw [value12, value16, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(63 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 134 = true ∨ valuation q 11 = true := by
  rw [value11, value12, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (63 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 14 = true := by
  rw [value13, value14, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(57 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (40 : Vertex) [(57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 135 = true ∨ valuation q 5 = true := by
  rw [value5, value13, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(40 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (57 : Vertex) [(40 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 136 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (56 : Vertex) → w ∈ [(59 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (56 : Vertex) [(59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 136 = true ∨ valuation q 13 = true := by
  rw [value13, value14, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(56 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (59 : Vertex) [(56 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 7 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value7, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (59 : Vertex) (43 : Vertex) (57 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 137 = true ∨ valuation q 14 = true ∨ valuation q 16 = true := by
  rw [value14, value15, value16, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(57 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (43 : Vertex) [(57 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 137 = true ∨ valuation q 7 = true ∨ valuation q 16 = true := by
  rw [value7, value15, value16, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(43 : Vertex), (63 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (57 : Vertex) [(43 : Vertex), (63 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 137 = true ∨ valuation q 7 = true ∨ valuation q 14 = true := by
  rw [value7, value14, value15, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(43 : Vertex), (57 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (63 : Vertex) [(43 : Vertex), (57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 138 = true ∨ valuation q 15 = true := by
  rw [value15, value16, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(59 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (55 : Vertex) [(59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 138 = true ∨ valuation q 12 = true := by
  rw [value12, value16, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(55 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (59 : Vertex) [(55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.First112
