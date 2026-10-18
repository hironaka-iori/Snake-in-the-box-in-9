import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 19 = false ∨ valuation q 86 = false := by
  rw [value14, value16, value19, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (164 : Vertex) (168 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 86 = true := by
  rw [value14, value15, value19, value86, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(161 : Vertex), (168 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (164 : Vertex) [(161 : Vertex), (168 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 86 = true := by
  rw [value14, value15, value16, value86, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(161 : Vertex), (164 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (168 : Vertex) [(161 : Vertex), (164 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 142 = true ∨ valuation q 15 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value14, value15, value16, value19, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(161 : Vertex), (164 : Vertex), (168 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (416 : Vertex) [(161 : Vertex), (164 : Vertex), (168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value1, value14, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (160 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 14 = false ∨ valuation q 87 = false := by
  rw [value1, value14, value15, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (160 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 20 = false ∨ valuation q 87 = false := by
  rw [value1, value15, value20, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (33 : Vertex) (169 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 143 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 87 = true := by
  rw [value14, value15, value20, value87, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (33 : Vertex) → w ∈ [(160 : Vertex), (169 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (33 : Vertex) [(160 : Vertex), (169 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 17 = true ∨ valuation q 22 = true ∨ valuation q 34 = true ∨ valuation q 90 = true := by
  rw [value16, value17, value22, value34, value90, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(166 : Vertex), (172 : Vertex), (228 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (160 : Vertex) [(166 : Vertex), (172 : Vertex), (228 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 34 = true ∨ valuation q 90 = true := by
  rw [value14, value16, value22, value34, value90, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(160 : Vertex), (172 : Vertex), (228 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (166 : Vertex) [(160 : Vertex), (172 : Vertex), (228 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 144 = true ∨ valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 22 = true ∨ valuation q 90 = true := by
  rw [value14, value16, value17, value22, value90, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(160 : Vertex), (166 : Vertex), (172 : Vertex), (420 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (228 : Vertex) [(160 : Vertex), (166 : Vertex), (172 : Vertex), (420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 23 = false := by
  rw [value16, value17, value18, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (164 : Vertex) (167 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value17, value18, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (167 : Vertex) (174 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 145 = true ∨ valuation q 18 = true ∨ valuation q 23 = true ∨ valuation q 25 = true := by
  rw [value17, value18, value23, value25, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(167 : Vertex), (174 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (164 : Vertex) [(167 : Vertex), (174 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 145 = true ∨ valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 25 = true := by
  rw [value16, value17, value18, value25, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(164 : Vertex), (167 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (174 : Vertex) [(164 : Vertex), (167 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 145 = true ∨ valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 23 = true := by
  rw [value16, value17, value18, value23, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(164 : Vertex), (167 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(164 : Vertex), (167 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 91 = false := by
  rw [value17, value18, value26, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (166 : Vertex) (183 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 26 = true ∨ valuation q 91 = true := by
  rw [value18, value26, value91, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(183 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (166 : Vertex) [(183 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 17 = true ∨ valuation q 91 = true := by
  rw [value17, value18, value91, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(166 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (183 : Vertex) [(166 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 27 = true := by
  rw [value19, value20, value22, value27, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(169 : Vertex), (172 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (160 : Vertex) [(169 : Vertex), (172 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 27 = true := by
  rw [value14, value19, value20, value27, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(160 : Vertex), (169 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (172 : Vertex) [(160 : Vertex), (169 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 28 = false := by
  rw [value15, value19, value20, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (168 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 92 = false := by
  rw [value15, value19, value20, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (168 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value15, value20, value21, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (171 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 21 = false ∨ valuation q 92 = false := by
  rw [value15, value20, value21, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (171 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value15, value20, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 28 = false ∨ valuation q 92 = false := by
  rw [value15, value20, value28, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 36 = false ∨ valuation q 92 = false := by
  rw [value15, value20, value36, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (233 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 28 = false := by
  rw [value19, value20, value21, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (171 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 36 = false := by
  rw [value19, value20, value21, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (171 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 92 = false := by
  rw [value19, value20, value21, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (171 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 36 = false := by
  rw [value19, value20, value28, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E034.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112034
