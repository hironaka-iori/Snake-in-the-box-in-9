import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 125 = true ∨ valuation q 1 = true ∨ valuation q 5 = true := by
  rw [value1, value5, value7, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(5 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (85 : Vertex) [(5 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 6 = true ∨ valuation q 11 = true := by
  rw [value6, value8, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ∈ [(19 : Vertex), (31 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (27 : Vertex) [(19 : Vertex), (31 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 6 = false ∨ valuation q 11 = false := by
  rw [value6, value11, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (27 : Vertex) (19 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 11 = true := by
  rw [value8, value11, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(31 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (19 : Vertex) [(31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 126 = true ∨ valuation q 6 = true := by
  rw [value6, value8, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(19 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (31 : Vertex) [(19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 10 = true := by
  rw [value9, value10, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (12 : Vertex) [(30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 127 = true ∨ valuation q 2 = true := by
  rw [value2, value9, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(12 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(12 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 128 = true ∨ valuation q 11 = true := by
  rw [value10, value11, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(31 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (28 : Vertex) [(31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 128 = true ∨ valuation q 9 = true := by
  rw [value9, value10, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (31 : Vertex) [(28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 10 = false := by
  rw [value4, value8, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 129 = true ∨ valuation q 4 = true ∨ valuation q 10 = true := by
  rw [value4, value10, value11, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(15 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (27 : Vertex) [(15 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 129 = true ∨ valuation q 4 = true ∨ valuation q 8 = true := by
  rw [value4, value8, value11, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(15 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (30 : Vertex) [(15 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 12 = true := by
  rw [value12, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (65 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = true ∨ valuation q 17 = true ∨ valuation q 50 = true := by
  rw [value12, value13, value17, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ∈ [(67 : Vertex), (73 : Vertex), (193 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (65 : Vertex) [(67 : Vertex), (73 : Vertex), (193 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 50 = false := by
  rw [value12, value13, value17, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (67 : Vertex) (73 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 13 = false ∨ valuation q 17 = false := by
  rw [value13, value17, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (65 : Vertex) (67 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 17 = true ∨ valuation q 50 = true := by
  rw [value12, value17, value50, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(73 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (67 : Vertex) [(73 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 50 = true := by
  rw [value12, value13, value50, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(67 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (73 : Vertex) [(67 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 130 = true ∨ valuation q 13 = true ∨ valuation q 17 = true := by
  rw [value12, value13, value17, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(67 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (193 : Vertex) [(67 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 52 = false := by
  rw [value12, value13, value15, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (65 : Vertex) (71 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 15 = true ∨ valuation q 52 = true := by
  rw [value13, value15, value52, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(71 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (65 : Vertex) [(71 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 52 = true := by
  rw [value12, value13, value52, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(65 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (71 : Vertex) [(65 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 15 = true := by
  rw [value12, value13, value15, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(65 : Vertex), (71 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (195 : Vertex) [(65 : Vertex), (71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 14 = true := by
  rw [value14, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (68 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 21 = true ∨ valuation q 53 = true := by
  rw [value14, value21, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ∈ [(84 : Vertex), (196 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (68 : Vertex) [(84 : Vertex), (196 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 21 = false ∨ valuation q 53 = false := by
  rw [value21, value53, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (68 : Vertex) (84 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 132 = true ∨ valuation q 53 = true := by
  rw [value14, value53, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(196 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 132 = true ∨ valuation q 21 = true := by
  rw [value14, value21, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (196 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 24 = false := by
  rw [value13, value15, value19, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (79 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 54 = false := by
  rw [value13, value15, value19, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (79 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 54 = false := by
  rw [value13, value15, value24, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (87 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 54 = false := by
  rw [value15, value19, value24, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (79 : Vertex) (87 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E158.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112158
