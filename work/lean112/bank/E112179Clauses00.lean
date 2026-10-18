import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 14 = false := by
  rw [value1, value2, value8, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (0 : Vertex) (1 : Vertex) (64 : Vertex) (128 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 105 = true ∨ valuation q 8 = true ∨ valuation q 14 = true := by
  rw [value1, value8, value14, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(64 : Vertex), (128 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(64 : Vertex), (128 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 106 = true ∨ valuation q 4 = true := by
  rw [value2, value4, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 106 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 7 = false ∨ valuation q 10 = false ∨ valuation q 17 = false := by
  rw [value3, value7, value10, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (22 : Vertex) (70 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 107 = true ∨ valuation q 10 = true ∨ valuation q 17 = true := by
  rw [value3, value10, value17, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(70 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(70 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 108 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(19 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (1 : Vertex) [(19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 108 = true ∨ valuation q 2 = true := by
  rw [value2, value4, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (19 : Vertex) [(1 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 109 = true ∨ valuation q 7 = true := by
  rw [value5, value7, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (19 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 109 = true ∨ valuation q 6 = true := by
  rw [value5, value6, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(19 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 110 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 110 = true ∨ valuation q 4 = true := by
  rw [value4, value6, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(17 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (18 : Vertex) [(17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 111 = true ∨ valuation q 5 = true := by
  rw [value5, value7, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 111 = true ∨ valuation q 3 = true := by
  rw [value3, value7, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 31 = false := by
  rw [value1, value8, value11, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (72 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 57 = false := by
  rw [value1, value8, value11, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (72 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 1 = false ∨ valuation q 31 = false ∨ valuation q 57 = false := by
  rw [value1, value8, value31, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (192 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 113 = true ∨ valuation q 8 = true := by
  rw [value8, value9, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(64 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (70 : Vertex) [(64 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 33 = false := by
  rw [value3, value10, value13, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (78 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 13 = false ∨ valuation q 59 = false := by
  rw [value3, value10, value13, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (78 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 33 = false ∨ valuation q 59 = false := by
  rw [value3, value10, value33, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (6 : Vertex) (198 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 33 = false ∨ valuation q 59 = false := by
  rw [value10, value13, value33, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (70 : Vertex) (78 : Vertex) (198 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 114 = true ∨ valuation q 3 = true ∨ valuation q 9 = true ∨ valuation q 13 = true ∨ valuation q 33 = true := by
  rw [value3, value9, value10, value13, value33, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(6 : Vertex), (66 : Vertex), (78 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (326 : Vertex) [(6 : Vertex), (66 : Vertex), (78 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 35 = false := by
  rw [value8, value11, value12, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (76 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 61 = false := by
  rw [value8, value11, value12, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (76 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 8 = false ∨ valuation q 35 = false ∨ valuation q 61 = false := by
  rw [value8, value11, value35, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (64 : Vertex) (200 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 35 = false ∨ valuation q 61 = false := by
  rw [value11, value12, value35, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (76 : Vertex) (200 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 11 = true ∨ valuation q 13 = true := by
  rw [value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (78 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (76 : Vertex) [(72 : Vertex), (78 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 116 = true ∨ valuation q 13 = true := by
  rw [value12, value13, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(78 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (72 : Vertex) [(78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 116 = true ∨ valuation q 11 = true := by
  rw [value11, value12, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (76 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(72 : Vertex)] := by decide
  have hg := other_cover q (76 : Vertex) (78 : Vertex) [(72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 117 = true ∨ valuation q 12 = true := by
  rw [value12, value13, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(76 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (70 : Vertex) [(76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 117 = true ∨ valuation q 10 = true := by
  rw [value10, value13, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (78 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(70 : Vertex)] := by decide
  have hg := other_cover q (78 : Vertex) (76 : Vertex) [(70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E179.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112179
