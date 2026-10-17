import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 115 = true ∨ valuation q 3 = true := by
  rw [value3, value7, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (44 : Vertex) w → w ∈ region → w ≠ (46 : Vertex) → w ∈ [(36 : Vertex)] := by decide
  have hg := other_cover q (44 : Vertex) (46 : Vertex) [(36 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 21 = false := by
  rw [value9, value10, value13, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (48 : Vertex) (52 : Vertex) (56 : Vertex) (112 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 120 = true ∨ valuation q 11 = true := by
  rw [value11, value12, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (63 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (63 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 121 = true ∨ valuation q 9 = true ∨ valuation q 26 = true := by
  rw [value9, value13, value26, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (56 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(48 : Vertex), (120 : Vertex)] := by decide
  have hg := other_cover q (56 : Vertex) (57 : Vertex) [(48 : Vertex), (120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 24 = false := by
  rw [value2, value19, value20, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (35 : Vertex) (98 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 46 = false := by
  rw [value19, value20, value24, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (98 : Vertex) (115 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 9 = false ∨ valuation q 22 = false ∨ valuation q 53 = false := by
  rw [value9, value21, value22, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (113 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value19, value21, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value19, value21, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (112 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 19 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value19, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (98 : Vertex) (115 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value21, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (114 : Vertex) (112 : Vertex) (115 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 132 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value24, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(113 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (99 : Vertex) [(113 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 132 = true ∨ valuation q 20 = true ∨ valuation q 23 = true := by
  rw [value20, value23, value24, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(99 : Vertex), (114 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (113 : Vertex) [(99 : Vertex), (114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 133 = true ∨ valuation q 23 = true := by
  rw [value23, value25, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(114 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (126 : Vertex) [(114 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value13, value21, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (56 : Vertex) (112 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ∈ [(120 : Vertex), (126 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (124 : Vertex) [(120 : Vertex), (126 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 27 = true := by
  rw [value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 136 = true ∨ valuation q 25 = true := by
  rw [value25, value28, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(118 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (124 : Vertex) [(118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 38 = false := by
  rw [value31, value32, value35, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 143 = true ∨ valuation q 31 = true := by
  rw [value31, value35, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(132 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (142 : Vertex) [(132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 78 = false := by
  rw [value37, value38, value41, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 31 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value31, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (144 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 148 = true ∨ valuation q 39 = true := by
  rw [value39, value40, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(149 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (159 : Vertex) [(149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 149 = true ∨ valuation q 37 = true := by
  rw [value37, value41, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (153 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 93 = false := by
  rw [value45, value46, value49, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (234 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value47, value48, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 155 = true ∨ valuation q 51 = true ∨ valuation q 54 = true := by
  rw [value47, value51, value54, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(236 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (229 : Vertex) [(236 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 155 = true ∨ valuation q 48 = true ∨ valuation q 51 = true := by
  rw [value47, value48, value51, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (228 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(229 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (228 : Vertex) (244 : Vertex) [(229 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 156 = true ∨ valuation q 47 = true ∨ valuation q 95 = true := by
  rw [value47, value48, value95, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (245 : Vertex) [(228 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 157 = true ∨ valuation q 45 = true ∨ valuation q 50 = true := by
  rw [value45, value49, value50, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (238 : Vertex) [(226 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 59 = false := by
  rw [value46, value49, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 96 = false := by
  rw [value46, value49, value50, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E190.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112190
