import E112182Semantics
import B112E182Inputs
namespace Snake9.Regrowth.E112182
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value4, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 107 = true ∨ valuation q 4 = true ∨ valuation q 21 = true ∨ valuation q 65 = true := by
  rw [value4, value5, value21, value65, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (41 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(40 : Vertex), (105 : Vertex), (297 : Vertex)] := by decide
  have hg := other_cover q (41 : Vertex) (57 : Vertex) [(40 : Vertex), (105 : Vertex), (297 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 122 = true ∨ valuation q 4 = true ∨ valuation q 21 = true ∨ valuation q 59 = true := by
  rw [value4, value20, value21, value59, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(40 : Vertex), (105 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (96 : Vertex) [(40 : Vertex), (105 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 17 = false ∨ valuation q 22 = false := by
  rw [value5, value17, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (97 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value17, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (104 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value25, value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (115 : Vertex) (118 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 128 = true ∨ valuation q 25 = true := by
  rw [value25, value26, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(114 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (113 : Vertex) [(114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 131 = true ∨ valuation q 31 = true := by
  rw [value29, value31, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value27, value28, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (126 : Vertex) (118 : Vertex) (122 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 48 = false := by
  rw [value35, value36, value37, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 48 = false := by
  rw [value35, value36, value38, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 75 = false := by
  rw [value35, value36, value38, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (140 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 48 = false := by
  rw [value35, value37, value38, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 43 = false ∨ valuation q 49 = false := by
  rw [value35, value36, value43, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (137 : Vertex) (136 : Vertex) (153 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 140 = true ∨ valuation q 35 = true ∨ valuation q 39 = true := by
  rw [value35, value38, value39, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(136 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(136 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 141 = true ∨ valuation q 37 = true := by
  rw [value37, value39, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (142 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(138 : Vertex)] := by decide
  have hg := other_cover q (142 : Vertex) (140 : Vertex) [(138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 142 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(149 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (132 : Vertex) [(149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 143 = true ∨ valuation q 42 = true := by
  rw [value41, value42, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (149 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(151 : Vertex)] := by decide
  have hg := other_cover q (149 : Vertex) (148 : Vertex) [(151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 34 = false ∨ valuation q 41 = false ∨ valuation q 46 = false := by
  rw [value34, value41, value42, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (135 : Vertex) (149 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 37 = false ∨ valuation q 45 = false ∨ valuation q 53 = false := by
  rw [value37, value44, value45, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (138 : Vertex) (155 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 83 = false := by
  rw [value44, value45, value53, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (154 : Vertex) (155 : Vertex) (218 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 147 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value45, value46, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(153 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (154 : Vertex) [(153 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 150 = true ∨ valuation q 35 = true ∨ valuation q 59 = true := by
  rw [value35, value48, value59, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(136 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (201 : Vertex) [(136 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 150 = true ∨ valuation q 35 = true ∨ valuation q 49 = true := by
  rw [value35, value48, value49, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(136 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (232 : Vertex) [(136 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 36 = false ∨ valuation q 48 = false ∨ valuation q 50 = false := by
  rw [value36, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 152 = true ∨ valuation q 51 = true ∨ valuation q 55 = true := by
  rw [value50, value51, value55, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (201 : Vertex) [(207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 152 = true ∨ valuation q 49 = true ∨ valuation q 55 = true := by
  rw [value49, value50, value55, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(201 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (207 : Vertex) [(201 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 152 = true ∨ valuation q 49 = true ∨ valuation q 51 = true := by
  rw [value49, value50, value51, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(201 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [(201 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 153 = true := by
  rw [value51, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (207 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (207 : Vertex) (205 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 154 = true ∨ valuation q 47 = true := by
  rw [value47, value52, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(198 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (222 : Vertex) [(198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 155 = true ∨ valuation q 56 = true := by
  rw [value53, value56, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 155 = true ∨ valuation q 44 = true := by
  rw [value44, value53, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(154 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (222 : Vertex) [(154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E182.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112182
