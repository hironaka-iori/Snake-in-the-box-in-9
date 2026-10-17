import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 126 = true ∨ valuation q 13 = true ∨ valuation q 50 = true := by
  rw [value12, value13, value50, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(78 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (68 : Vertex) [(78 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 126 = true ∨ valuation q 9 = true ∨ valuation q 50 = true := by
  rw [value9, value12, value50, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(68 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (78 : Vertex) [(68 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 126 = true ∨ valuation q 9 = true ∨ valuation q 13 = true := by
  rw [value9, value12, value13, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(68 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (204 : Vertex) [(68 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 52 = false := by
  rw [value11, value12, value13, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (74 : Vertex) (76 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 127 = true ∨ valuation q 12 = true ∨ valuation q 52 = true := by
  rw [value12, value13, value52, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(76 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (74 : Vertex) [(76 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 127 = true ∨ valuation q 11 = true ∨ valuation q 52 = true := by
  rw [value11, value13, value52, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(74 : Vertex), (206 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (76 : Vertex) [(74 : Vertex), (206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 54 = false := by
  rw [value14, value15, value18, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 15 = false ∨ valuation q 18 = false := by
  rw [value15, value18, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 128 = true ∨ valuation q 15 = true ∨ valuation q 54 = true := by
  rw [value14, value15, value54, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(84 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (88 : Vertex) [(84 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value9, value14, value15, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 129 = true ∨ valuation q 14 = true ∨ valuation q 16 = true := by
  rw [value14, value15, value16, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(80 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(80 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 129 = true ∨ valuation q 9 = true ∨ valuation q 16 = true := by
  rw [value9, value15, value16, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(68 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 129 = true ∨ valuation q 9 = true ∨ valuation q 14 = true := by
  rw [value9, value14, value15, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(68 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (85 : Vertex) [(68 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value15, value17, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (85 : Vertex) (84 : Vertex) (87 : Vertex) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 130 = true ∨ valuation q 17 = true := by
  rw [value16, value17, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (84 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 130 = true ∨ valuation q 15 = true := by
  rw [value15, value16, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (87 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 131 = true ∨ valuation q 22 = true := by
  rw [value17, value22, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 131 = true ∨ valuation q 16 = true := by
  rw [value16, value17, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (95 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value4, value14, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (24 : Vertex) (80 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value4, value14, value18, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (24 : Vertex) (80 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 59 = false := by
  rw [value4, value14, value18, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (24 : Vertex) (80 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value4, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (24 : Vertex) (89 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 59 = false := by
  rw [value4, value18, value19, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (24 : Vertex) (89 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value14, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (89 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 132 = true ∨ valuation q 14 = true ∨ valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 59 = true := by
  rw [value14, value18, value19, value20, value59, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(80 : Vertex), (89 : Vertex), (90 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (24 : Vertex) [(80 : Vertex), (89 : Vertex), (90 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 132 = true ∨ valuation q 4 = true ∨ valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 59 = true := by
  rw [value4, value18, value19, value20, value59, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(24 : Vertex), (89 : Vertex), (90 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(24 : Vertex), (89 : Vertex), (90 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 10 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value10, value18, value19, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 10 = false ∨ valuation q 18 = false ∨ valuation q 60 = false := by
  rw [value10, value18, value19, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (88 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 10 = false ∨ valuation q 21 = false ∨ valuation q 60 = false := by
  rw [value10, value19, value21, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (91 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 60 = false := by
  rw [value18, value19, value21, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (88 : Vertex) (91 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value18, value21, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (89 : Vertex) (88 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 133 = true ∨ valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 60 = true := by
  rw [value18, value19, value21, value60, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(88 : Vertex), (91 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (73 : Vertex) [(88 : Vertex), (91 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E168.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112168
