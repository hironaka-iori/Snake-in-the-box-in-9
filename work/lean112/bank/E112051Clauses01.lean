import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 129 = true ∨ valuation q 9 = true ∨ valuation q 16 = true := by
  rw [value9, value13, value16, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(17 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (27 : Vertex) [(17 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 129 = true ∨ valuation q 9 = true ∨ valuation q 15 = true := by
  rw [value9, value13, value15, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(17 : Vertex), (27 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (29 : Vertex) [(17 : Vertex), (27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (10 : Vertex) → w ∈ [(27 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (10 : Vertex) [(27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 6 = true := by
  rw [value6, value14, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(10 : Vertex)] := by decide
  have hg := other_cover q (26 : Vertex) (27 : Vertex) [(10 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 131 = true ∨ valuation q 14 = true := by
  rw [value14, value15, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(26 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (25 : Vertex) [(26 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 131 = true ∨ valuation q 13 = true := by
  rw [value13, value15, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (26 : Vertex) → w ∈ [(25 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (26 : Vertex) [(25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 132 = true ∨ valuation q 13 = true := by
  rw [value13, value16, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(25 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (21 : Vertex) [(25 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 132 = true ∨ valuation q 11 = true := by
  rw [value11, value16, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(21 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (25 : Vertex) [(21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 22 = false := by
  rw [value2, value17, value19, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (1 : Vertex) (73 : Vertex) (97 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 22 = true := by
  rw [value17, value18, value19, value22, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(69 : Vertex), (73 : Vertex), (97 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (1 : Vertex) [(69 : Vertex), (73 : Vertex), (97 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 2 = true ∨ valuation q 19 = true ∨ valuation q 22 = true := by
  rw [value2, value17, value19, value22, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(1 : Vertex), (73 : Vertex), (97 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (69 : Vertex) [(1 : Vertex), (73 : Vertex), (97 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 2 = true ∨ valuation q 18 = true ∨ valuation q 22 = true := by
  rw [value2, value17, value18, value22, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(1 : Vertex), (69 : Vertex), (97 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (73 : Vertex) [(1 : Vertex), (69 : Vertex), (97 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 134 = true := by
  rw [value18, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (69 : Vertex) (65 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 19 = true := by
  rw [value19, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (73 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = true ∨ valuation q 20 = true := by
  rw [value17, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ∈ [(65 : Vertex), (75 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (73 : Vertex) [(65 : Vertex), (75 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 20 = true := by
  rw [value19, value20, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (65 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 17 = true := by
  rw [value17, value19, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(65 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (75 : Vertex) [(65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 21 = true := by
  rw [value20, value21, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (73 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 19 = true := by
  rw [value19, value20, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(73 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (79 : Vertex) [(73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 8 = false ∨ valuation q 20 = false ∨ valuation q 26 = false := by
  rw [value8, value20, value21, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (15 : Vertex) (75 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 20 = true ∨ valuation q 26 = true := by
  rw [value20, value21, value26, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(75 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (15 : Vertex) [(75 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 8 = true ∨ valuation q 26 = true := by
  rw [value8, value21, value26, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(15 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (75 : Vertex) [(15 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 8 = true ∨ valuation q 20 = true := by
  rw [value8, value20, value21, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(15 : Vertex), (75 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (111 : Vertex) [(15 : Vertex), (75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 67 = false := by
  rw [value17, value22, value27, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (97 : Vertex) (65 : Vertex) (113 : Vertex) (353 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 27 = true ∨ valuation q 67 = true := by
  rw [value22, value27, value67, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (97 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(113 : Vertex), (353 : Vertex)] := by decide
  have hg := other_cover q (97 : Vertex) (65 : Vertex) [(113 : Vertex), (353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 139 = true := by
  rw [value23, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (104 : Vertex) (106 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 25 = true ∨ valuation q 29 = true := by
  rw [value24, value25, value29, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(110 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (104 : Vertex) [(110 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 29 = true := by
  rw [value23, value24, value29, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (110 : Vertex) → w ∈ [(104 : Vertex), (122 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (110 : Vertex) [(104 : Vertex), (122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 25 = true := by
  rw [value23, value24, value25, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (106 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(104 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (106 : Vertex) (122 : Vertex) [(104 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 74 = false := by
  rw [value24, value25, value26, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (106 : Vertex) (111 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 141 = true ∨ valuation q 26 = true ∨ valuation q 74 = true := by
  rw [value25, value26, value74, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(111 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (106 : Vertex) [(111 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 75 = false := by
  rw [value21, value25, value26, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (79 : Vertex) (110 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E051.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112051
