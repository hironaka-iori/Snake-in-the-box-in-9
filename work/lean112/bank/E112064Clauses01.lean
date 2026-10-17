import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 125 = true ∨ valuation q 3 = true ∨ valuation q 16 = true := by
  rw [value3, value8, value16, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (74 : Vertex) → w ∈ [(70 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (74 : Vertex) [(70 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 125 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value3, value6, value8, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(70 : Vertex), (74 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (94 : Vertex) [(70 : Vertex), (74 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 9 = true := by
  rw [value9, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (80 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = true ∨ valuation q 37 = true ∨ valuation q 74 = true := by
  rw [value9, value13, value37, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ∈ [(88 : Vertex), (208 : Vertex), (336 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (80 : Vertex) [(88 : Vertex), (208 : Vertex), (336 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 37 = false ∨ valuation q 74 = false := by
  rw [value9, value13, value37, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (88 : Vertex) (208 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 37 = true ∨ valuation q 74 = true := by
  rw [value9, value37, value74, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(208 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (88 : Vertex) [(208 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 13 = true ∨ valuation q 74 = true := by
  rw [value9, value13, value74, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(88 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (208 : Vertex) [(88 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 13 = true ∨ valuation q 37 = true := by
  rw [value9, value13, value37, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(88 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (336 : Vertex) [(88 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 10 = true := by
  rw [value10, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (83 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = true ∨ valuation q 76 = true := by
  rw [value10, value12, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ∈ [(87 : Vertex), (339 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (83 : Vertex) [(87 : Vertex), (339 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 12 = false ∨ valuation q 76 = false := by
  rw [value12, value76, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (83 : Vertex) (87 : Vertex) (339 : Vertex) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 127 = true ∨ valuation q 76 = true := by
  rw [value10, value76, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(339 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (87 : Vertex) [(339 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 127 = true ∨ valuation q 12 = true := by
  rw [value10, value12, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (339 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (339 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 2 = false ∨ valuation q 12 = false ∨ valuation q 15 = false := by
  rw [value2, value11, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (69 : Vertex) (87 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 2 = false ∨ valuation q 15 = false := by
  rw [value2, value15, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (85 : Vertex) (69 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 12 = true ∨ valuation q 15 = true := by
  rw [value11, value12, value15, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(87 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (69 : Vertex) [(87 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 2 = true ∨ valuation q 15 = true := by
  rw [value2, value11, value15, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(69 : Vertex), (93 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (87 : Vertex) [(69 : Vertex), (93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 79 = false := by
  rw [value10, value11, value12, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (83 : Vertex) (85 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 129 = true ∨ valuation q 11 = true ∨ valuation q 79 = true := by
  rw [value11, value12, value79, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(85 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (83 : Vertex) [(85 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 129 = true ∨ valuation q 10 = true ∨ valuation q 79 = true := by
  rw [value10, value12, value79, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(83 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(83 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 129 = true ∨ valuation q 10 = true ∨ valuation q 11 = true := by
  rw [value10, value11, value12, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(83 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (343 : Vertex) [(83 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 42 = false := by
  rw [value4, value13, value14, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (89 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 80 = false := by
  rw [value4, value13, value14, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (89 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 9 = true ∨ valuation q 14 = true ∨ valuation q 42 = true ∨ valuation q 80 = true := by
  rw [value9, value13, value14, value42, value80, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(80 : Vertex), (89 : Vertex), (216 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (72 : Vertex) [(80 : Vertex), (89 : Vertex), (216 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 14 = true ∨ valuation q 42 = true ∨ valuation q 80 = true := by
  rw [value4, value13, value14, value42, value80, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(72 : Vertex), (89 : Vertex), (216 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(72 : Vertex), (89 : Vertex), (216 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 42 = true ∨ valuation q 80 = true := by
  rw [value4, value9, value13, value42, value80, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(72 : Vertex), (80 : Vertex), (216 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (89 : Vertex) [(72 : Vertex), (80 : Vertex), (216 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 14 = true ∨ valuation q 80 = true := by
  rw [value4, value9, value13, value14, value80, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(72 : Vertex), (80 : Vertex), (89 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (216 : Vertex) [(72 : Vertex), (80 : Vertex), (89 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 9 = true ∨ valuation q 14 = true ∨ valuation q 42 = true := by
  rw [value4, value9, value13, value14, value42, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(72 : Vertex), (80 : Vertex), (89 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (344 : Vertex) [(72 : Vertex), (80 : Vertex), (89 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 15 = false := by
  rw [value5, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (88 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 5 = false ∨ valuation q 13 = false ∨ valuation q 81 = false := by
  rw [value5, value13, value14, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (88 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 5 = false ∨ valuation q 15 = false ∨ valuation q 81 = false := by
  rw [value5, value14, value15, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (73 : Vertex) (93 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 81 = false := by
  rw [value13, value14, value15, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (88 : Vertex) (93 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E064.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112064
