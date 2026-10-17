import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 107 = true := by
  rw [value1, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 108 = true ∨ valuation q 1 = true ∨ valuation q 3 = true ∨ valuation q 6 = true := by
  rw [value1, value2, value3, value6, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (5 : Vertex), (9 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (5 : Vertex), (9 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 7 = false := by
  rw [value2, value3, value5, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (1 : Vertex) (7 : Vertex) (13 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 12 = false ∨ valuation q 34 = false := by
  rw [value4, value5, value12, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (7 : Vertex) (22 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 34 = false ∨ valuation q 48 = false := by
  rw [value4, value5, value34, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (7 : Vertex) (134 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 12 = false ∨ valuation q 34 = false ∨ valuation q 48 = false := by
  rw [value4, value12, value34, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (22 : Vertex) (134 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 111 = true ∨ valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 8 = true := by
  rw [value3, value4, value5, value8, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (7 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(5 : Vertex), (6 : Vertex), (15 : Vertex)] := by decide
  have hg := other_cover q (7 : Vertex) (263 : Vertex) [(5 : Vertex), (6 : Vertex), (15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 15 = false := by
  rw [value6, value7, value8, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (9 : Vertex) (15 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value10, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (19 : Vertex) (22 : Vertex) (26 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 117 = true ∨ valuation q 10 = true := by
  rw [value10, value11, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 118 = true ∨ valuation q 4 = true ∨ valuation q 10 = true := by
  rw [value4, value10, value12, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(6 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (30 : Vertex) [(6 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 120 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 127 = true ∨ valuation q 22 = true ∨ valuation q 73 = true := by
  rw [value21, value22, value73, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(105 : Vertex), (360 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (96 : Vertex) [(105 : Vertex), (360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value18, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (104 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 135 = true ∨ valuation q 32 = true := by
  rw [value29, value32, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (114 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 136 = true ∨ valuation q 32 = true := by
  rw [value30, value32, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value28, value29, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (118 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 139 = true := by
  rw [value33, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (130 : Vertex) (134 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 4 = false ∨ valuation q 36 = false ∨ valuation q 45 = false := by
  rw [value4, value34, value36, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (166 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 140 = true ∨ valuation q 4 = true ∨ valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 36 = true := by
  rw [value4, value33, value34, value35, value36, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(6 : Vertex), (130 : Vertex), (142 : Vertex), (166 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (198 : Vertex) [(6 : Vertex), (130 : Vertex), (142 : Vertex), (166 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 141 = true := by
  rw [value35, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (142 : Vertex) (134 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 40 = false ∨ valuation q 78 = false := by
  rw [value34, value36, value40, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (134 : Vertex) (182 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 142 = true ∨ valuation q 40 = true ∨ valuation q 78 = true := by
  rw [value36, value40, value78, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(182 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (134 : Vertex) [(182 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 144 = true ∨ valuation q 39 = true ∨ valuation q 43 = true := by
  rw [value38, value39, value43, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (169 : Vertex) [(175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 145 = true := by
  rw [value39, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 146 = true ∨ valuation q 44 = true := by
  rw [value40, value44, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 146 = true ∨ valuation q 36 = true := by
  rw [value36, value40, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(166 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (190 : Vertex) [(166 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 147 = true ∨ valuation q 88 = true := by
  rw [value41, value88, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (190 : Vertex) [(442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 148 = true ∨ valuation q 44 = true := by
  rw [value42, value44, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 149 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(188 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value40, value41, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (182 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 150 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value44, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(182 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (190 : Vertex) (188 : Vertex) [(182 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E249.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112249
