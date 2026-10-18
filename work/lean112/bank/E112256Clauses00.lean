import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 1 = true := by
  rw [value1, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (65 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = true ∨ valuation q 6 = true ∨ valuation q 37 = true := by
  rw [value1, value3, value6, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ∈ [(69 : Vertex), (73 : Vertex), (193 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (65 : Vertex) [(69 : Vertex), (73 : Vertex), (193 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 37 = false := by
  rw [value1, value3, value6, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (65 : Vertex) (69 : Vertex) (73 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 3 = false ∨ valuation q 37 = false := by
  rw [value3, value37, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (65 : Vertex) (69 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 128 = true ∨ valuation q 6 = true ∨ valuation q 37 = true := by
  rw [value1, value6, value37, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(73 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (69 : Vertex) [(73 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 128 = true ∨ valuation q 3 = true ∨ valuation q 37 = true := by
  rw [value1, value3, value37, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(69 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (73 : Vertex) [(69 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 128 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value1, value3, value6, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (65 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(69 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (65 : Vertex) (193 : Vertex) [(69 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 2 = true := by
  rw [value2, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (66 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = true ∨ valuation q 20 = true ∨ valuation q 38 = true := by
  rw [value2, value4, value20, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ∈ [(70 : Vertex), (98 : Vertex), (194 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (66 : Vertex) [(70 : Vertex), (98 : Vertex), (194 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 20 = false ∨ valuation q 38 = false := by
  rw [value20, value38, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (66 : Vertex) (98 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 129 = true ∨ valuation q 4 = true ∨ valuation q 38 = true := by
  rw [value2, value4, value38, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (98 : Vertex) → w ∈ [(70 : Vertex), (194 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (98 : Vertex) [(70 : Vertex), (194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 129 = true ∨ valuation q 4 = true ∨ valuation q 20 = true := by
  rw [value2, value4, value20, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (66 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(70 : Vertex), (98 : Vertex)] := by decide
  have hg := other_cover q (66 : Vertex) (194 : Vertex) [(70 : Vertex), (98 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 130 = true ∨ valuation q 21 = true := by
  rw [value3, value21, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(101 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (65 : Vertex) [(101 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 130 = true ∨ valuation q 1 = true := by
  rw [value1, value3, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(65 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (101 : Vertex) [(65 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 131 = true := by
  rw [value4, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (66 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (70 : Vertex) (66 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 5 = true := by
  rw [value5, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (72 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = true ∨ valuation q 8 = true ∨ valuation q 40 = true := by
  rw [value5, value6, value8, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ∈ [(73 : Vertex), (76 : Vertex), (200 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (72 : Vertex) [(73 : Vertex), (76 : Vertex), (200 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 40 = false := by
  rw [value5, value6, value8, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (73 : Vertex) (76 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 8 = false ∨ valuation q 40 = false := by
  rw [value8, value40, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (72 : Vertex) (76 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 132 = true ∨ valuation q 8 = true ∨ valuation q 40 = true := by
  rw [value5, value8, value40, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(76 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (73 : Vertex) [(76 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 132 = true ∨ valuation q 6 = true ∨ valuation q 40 = true := by
  rw [value5, value6, value40, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(73 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (76 : Vertex) [(73 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 132 = true ∨ valuation q 6 = true ∨ valuation q 8 = true := by
  rw [value5, value6, value8, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(73 : Vertex), (76 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (200 : Vertex) [(73 : Vertex), (76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 7 = false := by
  rw [value1, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (72 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 14 = false := by
  rw [value1, value5, value6, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (72 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 23 = false := by
  rw [value1, value5, value6, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (72 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 41 = false := by
  rw [value1, value5, value6, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (72 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 78 = false := by
  rw [value1, value5, value6, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (72 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 14 = false := by
  rw [value1, value6, value7, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (75 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 23 = false := by
  rw [value1, value6, value7, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (75 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 41 = false := by
  rw [value1, value6, value7, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (75 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 78 = false := by
  rw [value1, value6, value7, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (75 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 23 = false := by
  rw [value1, value6, value14, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (73 : Vertex) (65 : Vertex) (89 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E256.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112256
