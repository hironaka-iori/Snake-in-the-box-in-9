import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 108 = true := by
  rw [value1, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (0 : Vertex) (2 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 109 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (18 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 110 = true ∨ valuation q 4 = true ∨ valuation q 51 = true := by
  rw [value3, value4, value51, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(26 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (2 : Vertex) [(26 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 110 = true ∨ valuation q 2 = true ∨ valuation q 51 = true := by
  rw [value2, value3, value51, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (26 : Vertex) → w ∈ [(2 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (26 : Vertex) [(2 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 110 = true ∨ valuation q 2 = true ∨ valuation q 4 = true := by
  rw [value2, value3, value4, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(2 : Vertex), (26 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (274 : Vertex) [(2 : Vertex), (26 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 56 = false := by
  rw [value3, value4, value5, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (26 : Vertex) (18 : Vertex) (58 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 4 = false ∨ valuation q 8 = false ∨ valuation q 21 = false := by
  rw [value4, value5, value8, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (58 : Vertex) (26 : Vertex) (122 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 112 = true ∨ valuation q 4 = true ∨ valuation q 21 = true := by
  rw [value4, value5, value21, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (58 : Vertex) w → w ∈ region → w ≠ (122 : Vertex) → w ∈ [(26 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (58 : Vertex) (122 : Vertex) [(26 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 113 = true ∨ valuation q 9 = true := by
  rw [value6, value9, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (119 : Vertex) → w ∈ [(123 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (119 : Vertex) [(123 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 6 = true := by
  rw [value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (119 : Vertex) w → w ∈ region → w ∈ [(115 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (119 : Vertex) [(115 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 7 = true := by
  rw [value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 115 = true ∨ valuation q 5 = true := by
  rw [value5, value8, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (122 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(58 : Vertex)] := by decide
  have hg := other_cover q (122 : Vertex) (123 : Vertex) [(58 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 116 = true ∨ valuation q 8 = true := by
  rw [value8, value9, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (123 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(122 : Vertex)] := by decide
  have hg := other_cover q (123 : Vertex) (115 : Vertex) [(122 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 117 = true ∨ valuation q 12 = true := by
  rw [value10, value12, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(162 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(162 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 117 = true ∨ valuation q 11 = true := by
  rw [value10, value11, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(161 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (162 : Vertex) [(161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 118 = true ∨ valuation q 75 = true := by
  rw [value11, value75, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 118 = true ∨ valuation q 10 = true := by
  rw [value10, value11, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(160 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (417 : Vertex) [(160 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 17 = false := by
  rw [value10, value12, value13, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (166 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 119 = true ∨ valuation q 13 = true ∨ valuation q 17 = true := by
  rw [value12, value13, value17, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(166 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(166 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 78 = false := by
  rw [value12, value13, value16, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (174 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 121 = true ∨ valuation q 16 = true ∨ valuation q 23 = true := by
  rw [value14, value16, value23, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(174 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (173 : Vertex) [(174 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value12, value17, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 12 = false ∨ valuation q 21 = false ∨ valuation q 85 = false := by
  rw [value12, value17, value21, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (186 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 22 = false := by
  rw [value17, value18, value20, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (178 : Vertex) (183 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 125 = true ∨ valuation q 17 = true ∨ valuation q 22 = true := by
  rw [value17, value18, value22, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(178 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (183 : Vertex) [(178 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 126 = true ∨ valuation q 20 = true := by
  rw [value19, value20, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(183 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (189 : Vertex) [(183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 127 = true ∨ valuation q 18 = true := by
  rw [value18, value20, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(179 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (181 : Vertex) [(179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 17 = false ∨ valuation q 22 = false := by
  rw [value5, value17, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (58 : Vertex) (178 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 5 = false ∨ valuation q 22 = false ∨ valuation q 90 = false := by
  rw [value5, value21, value22, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (58 : Vertex) (187 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 128 = true ∨ valuation q 17 = true ∨ valuation q 22 = true ∨ valuation q 90 = true := by
  rw [value17, value21, value22, value90, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (58 : Vertex) → w ∈ [(178 : Vertex), (187 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (58 : Vertex) [(178 : Vertex), (187 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 91 = false := by
  rw [value18, value21, value22, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (179 : Vertex) (186 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 129 = true ∨ valuation q 21 = true ∨ valuation q 91 = true := by
  rw [value21, value22, value91, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(186 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (179 : Vertex) [(186 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E151.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112151
