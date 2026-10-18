import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 71 = false := by
  rw [value18, value21, value24, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (117 : Vertex) (113 : Vertex) (125 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 141 = true ∨ valuation q 24 = true ∨ valuation q 71 = true := by
  rw [value21, value24, value71, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (117 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(125 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (117 : Vertex) (113 : Vertex) [(125 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 24 = false := by
  rw [value15, value18, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (121 : Vertex) (105 : Vertex) (113 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 143 = true ∨ valuation q 25 = true := by
  rw [value23, value25, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(126 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (125 : Vertex) [(126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 143 = true ∨ valuation q 24 = true := by
  rw [value23, value24, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (124 : Vertex) w → w ∈ region → w ≠ (126 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (124 : Vertex) (126 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value21, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (125 : Vertex) (117 : Vertex) (121 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 144 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value24, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (117 : Vertex) → w ∈ [(121 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (117 : Vertex) [(121 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 145 = true ∨ valuation q 16 = true := by
  rw [value16, value25, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (126 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(110 : Vertex)] := by decide
  have hg := other_cover q (126 : Vertex) (124 : Vertex) [(110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 146 = true ∨ valuation q 30 = true := by
  rw [value26, value30, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (162 : Vertex) → w ∈ [(168 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (162 : Vertex) [(168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 147 = true ∨ valuation q 28 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value27, value28, value32, value36, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(166 : Vertex), (170 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(166 : Vertex), (170 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 147 = true ∨ valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 32 = true := by
  rw [value26, value27, value28, value32, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(160 : Vertex), (166 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (178 : Vertex) [(160 : Vertex), (166 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 33 = false := by
  rw [value27, value28, value29, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (167 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 47 = false := by
  rw [value27, value28, value29, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (167 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 81 = false := by
  rw [value27, value28, value29, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (167 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 47 = false ∨ valuation q 81 = false := by
  rw [value28, value33, value47, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (174 : Vertex) (230 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 149 = true ∨ valuation q 28 = true ∨ valuation q 34 = true ∨ valuation q 82 = true := by
  rw [value28, value29, value34, value82, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (39 : Vertex) → w ∈ [(166 : Vertex), (175 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (39 : Vertex) [(166 : Vertex), (175 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 150 = true ∨ valuation q 31 = true ∨ valuation q 32 = true ∨ valuation q 83 = true := by
  rw [value30, value31, value32, value83, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(169 : Vertex), (170 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (160 : Vertex) [(169 : Vertex), (170 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 150 = true ∨ valuation q 26 = true ∨ valuation q 31 = true ∨ valuation q 83 = true := by
  rw [value26, value30, value31, value83, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(160 : Vertex), (169 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (170 : Vertex) [(160 : Vertex), (169 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 8 = false ∨ valuation q 30 = false ∨ valuation q 84 = false := by
  rw [value8, value30, value31, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (168 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value27, value30, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (162 : Vertex) (168 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 48 = false := by
  rw [value27, value30, value32, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (162 : Vertex) (168 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 27 = false ∨ valuation q 33 = false ∨ valuation q 48 = false := by
  rw [value27, value32, value33, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (162 : Vertex) (174 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 48 = false := by
  rw [value30, value32, value33, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (168 : Vertex) (174 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 153 = true ∨ valuation q 28 = true ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value28, value32, value33, value34, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (174 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(166 : Vertex), (170 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (174 : Vertex) (190 : Vertex) [(166 : Vertex), (170 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 88 = false := by
  rw [value29, value33, value34, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (174 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value35, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (179 : Vertex) (181 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 155 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value35, value38, value39, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(181 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (179 : Vertex) [(181 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 27 = false ∨ valuation q 37 = false ∨ valuation q 90 = false := by
  rw [value27, value36, value37, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 157 = true ∨ valuation q 36 = true := by
  rw [value36, value37, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 157 = true ∨ valuation q 35 = true := by
  rw [value35, value37, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(177 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 92 = false := by
  rw [value35, value38, value41, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (177 : Vertex) (189 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 41 = false := by
  rw [value31, value35, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (177 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E152.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112152
