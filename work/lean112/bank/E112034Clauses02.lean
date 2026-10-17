import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 92 = false := by
  rw [value19, value20, value28, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 36 = false ∨ valuation q 92 = false := by
  rw [value19, value20, value36, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value20, value21, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 92 = false := by
  rw [value20, value21, value28, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 36 = false ∨ valuation q 92 = false := by
  rw [value20, value21, value36, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 36 = false ∨ valuation q 92 = false := by
  rw [value20, value28, value36, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (185 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 28 = true ∨ valuation q 92 = true := by
  rw [value15, value19, value20, value21, value28, value92, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (169 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(161 : Vertex), (168 : Vertex), (171 : Vertex), (185 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (169 : Vertex) (233 : Vertex) [(161 : Vertex), (168 : Vertex), (171 : Vertex), (185 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 149 = true ∨ valuation q 20 = true ∨ valuation q 30 = true ∨ valuation q 38 = true := by
  rw [value20, value21, value30, value38, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(169 : Vertex), (187 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (43 : Vertex) [(169 : Vertex), (187 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 149 = true ∨ valuation q 4 = true ∨ valuation q 20 = true ∨ valuation q 38 = true := by
  rw [value4, value20, value21, value38, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(43 : Vertex), (169 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (187 : Vertex) [(43 : Vertex), (169 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 19 = true ∨ valuation q 23 = true := by
  rw [value19, value22, value23, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(168 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (164 : Vertex) [(168 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 16 = true ∨ valuation q 23 = true := by
  rw [value16, value22, value23, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(164 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (168 : Vertex) [(164 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value19, value22, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(164 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (174 : Vertex) [(164 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 151 = true ∨ valuation q 22 = true := by
  rw [value22, value23, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(172 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (166 : Vertex) [(172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 151 = true ∨ valuation q 17 = true := by
  rw [value17, value23, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(166 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (172 : Vertex) [(166 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 152 = true ∨ valuation q 31 = true := by
  rw [value24, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(189 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (183 : Vertex) [(189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 152 = true ∨ valuation q 26 = true := by
  rw [value24, value26, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(183 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (189 : Vertex) [(183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 45 = false := by
  rw [value17, value25, value26, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (166 : Vertex) (183 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 153 = true ∨ valuation q 26 = true ∨ valuation q 45 = true := by
  rw [value25, value26, value45, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(183 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(183 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 153 = true ∨ valuation q 17 = true ∨ valuation q 26 = true := by
  rw [value17, value25, value26, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(166 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (246 : Vertex) [(166 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value18, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (181 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 154 = true ∨ valuation q 24 = true ∨ valuation q 25 = true := by
  rw [value24, value25, value26, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(181 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (167 : Vertex) [(181 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 154 = true ∨ valuation q 18 = true ∨ valuation q 25 = true := by
  rw [value18, value25, value26, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(167 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (181 : Vertex) [(167 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 154 = true ∨ valuation q 18 = true ∨ valuation q 24 = true := by
  rw [value18, value24, value26, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(167 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (182 : Vertex) [(167 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 19 = false ∨ valuation q 28 = false := by
  rw [value9, value19, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (168 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 19 = false ∨ valuation q 29 = false := by
  rw [value9, value19, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (168 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 19 = false ∨ valuation q 46 = false := by
  rw [value9, value19, value27, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (168 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value9, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value9, value27, value28, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (185 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 29 = false ∨ valuation q 46 = false := by
  rw [value9, value27, value29, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (56 : Vertex) (186 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value19, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 46 = false := by
  rw [value19, value27, value28, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (185 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 46 = false := by
  rw [value27, value28, value29, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (185 : Vertex) (186 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E034.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112034
