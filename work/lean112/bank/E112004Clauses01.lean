import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 26 = false ∨ valuation q 46 = false := by
  rw [value10, value12, value26, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (51 : Vertex) (55 : Vertex) (115 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 12 = false ∨ valuation q 26 = false := by
  rw [value12, value26, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (51 : Vertex) (55 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 12 = false ∨ valuation q 46 = false := by
  rw [value12, value46, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (51 : Vertex) (55 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 130 = true ∨ valuation q 26 = true ∨ valuation q 46 = true := by
  rw [value10, value26, value46, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (51 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(115 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (51 : Vertex) (55 : Vertex) [(115 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 2 = false ∨ valuation q 12 = false := by
  rw [value2, value12, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (53 : Vertex) (37 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 131 = true ∨ valuation q 12 = true := by
  rw [value11, value12, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (37 : Vertex) [(55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 16 = false := by
  rw [value10, value11, value12, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (51 : Vertex) (53 : Vertex) (63 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = false ∨ valuation q 16 = false ∨ valuation q 49 = false := by
  rw [value11, value12, value16, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (55 : Vertex) (53 : Vertex) (63 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 132 = true ∨ valuation q 10 = true ∨ valuation q 16 = true ∨ valuation q 49 = true := by
  rw [value10, value12, value16, value49, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(51 : Vertex), (63 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(51 : Vertex), (63 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 29 = false ∨ valuation q 50 = false := by
  rw [value13, value14, value29, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (56 : Vertex) (57 : Vertex) (120 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 133 = true ∨ valuation q 9 = true ∨ valuation q 14 = true ∨ valuation q 29 = true ∨ valuation q 50 = true := by
  rw [value9, value13, value14, value29, value50, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(48 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (40 : Vertex) [(48 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 14 = true ∨ valuation q 29 = true ∨ valuation q 50 = true := by
  rw [value4, value13, value14, value29, value50, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(40 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (48 : Vertex) [(40 : Vertex), (57 : Vertex), (120 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 29 = true ∨ valuation q 50 = true := by
  rw [value4, value9, value13, value29, value50, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(40 : Vertex), (48 : Vertex), (120 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (57 : Vertex) [(40 : Vertex), (48 : Vertex), (120 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 14 = true ∨ valuation q 50 = true := by
  rw [value4, value9, value13, value14, value50, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(40 : Vertex), (48 : Vertex), (57 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (120 : Vertex) [(40 : Vertex), (48 : Vertex), (57 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 133 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 14 = true ∨ valuation q 29 = true := by
  rw [value4, value9, value13, value14, value29, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(40 : Vertex), (48 : Vertex), (57 : Vertex), (120 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (184 : Vertex) [(40 : Vertex), (48 : Vertex), (57 : Vertex), (120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 51 = false := by
  rw [value5, value13, value14, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (41 : Vertex) (56 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 5 = false ∨ valuation q 13 = false := by
  rw [value5, value13, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (57 : Vertex) (41 : Vertex) (56 : Vertex) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 134 = true ∨ valuation q 13 = true ∨ valuation q 51 = true := by
  rw [value13, value14, value51, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(56 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (41 : Vertex) [(56 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 134 = true ∨ valuation q 5 = true ∨ valuation q 51 = true := by
  rw [value5, value14, value51, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (56 : Vertex) → w ∈ [(41 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (56 : Vertex) [(41 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 55 = false := by
  rw [value8, value15, value16, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (46 : Vertex) (63 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 135 = true ∨ valuation q 16 = true ∨ valuation q 55 = true := by
  rw [value15, value16, value55, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(63 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (46 : Vertex) [(63 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 135 = true ∨ valuation q 8 = true ∨ valuation q 55 = true := by
  rw [value8, value15, value55, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(46 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (63 : Vertex) [(46 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 16 = true := by
  rw [value16, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (63 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 56 = false := by
  rw [value12, value15, value16, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (62 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 78 = false := by
  rw [value12, value15, value16, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (62 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 12 = false ∨ valuation q 56 = false ∨ valuation q 78 = false := by
  rw [value12, value16, value56, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (55 : Vertex) (191 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 56 = false ∨ valuation q 78 = false := by
  rw [value15, value16, value56, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (63 : Vertex) (62 : Vertex) (191 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 136 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 56 = true := by
  rw [value12, value15, value16, value56, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (63 : Vertex) w → w ∈ region → w ≠ (319 : Vertex) → w ∈ [(55 : Vertex), (62 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (63 : Vertex) (319 : Vertex) [(55 : Vertex), (62 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 17 = true := by
  rw [value17, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (96 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value17, value18, value21, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (96 : Vertex) (97 : Vertex) (104 : Vertex) (112 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value18, value21, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (96 : Vertex) (97 : Vertex) (104 : Vertex) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 137 = true ∨ valuation q 21 = true ∨ valuation q 24 = true := by
  rw [value17, value21, value24, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (96 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(104 : Vertex), (112 : Vertex)] := by decide
  have hg := other_cover q (96 : Vertex) (97 : Vertex) [(104 : Vertex), (112 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E004.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112004
