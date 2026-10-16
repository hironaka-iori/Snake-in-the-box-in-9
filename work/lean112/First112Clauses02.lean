import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 39 = false := by
  rw [value2, value17, value19, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (35 : Vertex) (103 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 2 = false ∨ valuation q 39 = false ∨ valuation q 73 = false := by
  rw [value2, value17, value39, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (99 : Vertex) (35 : Vertex) (227 : Vertex) (355 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 139 = true ∨ valuation q 19 = true ∨ valuation q 39 = true ∨ valuation q 73 = true := by
  rw [value17, value19, value39, value73, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(103 : Vertex), (227 : Vertex), (355 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (35 : Vertex) [(103 : Vertex), (227 : Vertex), (355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 139 = true ∨ valuation q 2 = true ∨ valuation q 19 = true ∨ valuation q 39 = true := by
  rw [value2, value17, value19, value39, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (99 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(35 : Vertex), (103 : Vertex), (227 : Vertex)] := by decide
  have hg := other_cover q (99 : Vertex) (355 : Vertex) [(35 : Vertex), (103 : Vertex), (227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 3 = false ∨ valuation q 40 = false ∨ valuation q 74 = false := by
  rw [value3, value18, value40, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (100 : Vertex) (36 : Vertex) (228 : Vertex) (356 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 140 = true ∨ valuation q 3 = true ∨ valuation q 40 = true := by
  rw [value3, value18, value40, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (100 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(36 : Vertex), (228 : Vertex)] := by decide
  have hg := other_cover q (100 : Vertex) (356 : Vertex) [(36 : Vertex), (228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 75 = true := by
  rw [value19, value75, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (99 : Vertex) → w ∈ [(359 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (99 : Vertex) [(359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 141 = true ∨ valuation q 17 = true := by
  rw [value17, value19, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (103 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(99 : Vertex)] := by decide
  have hg := other_cover q (103 : Vertex) (359 : Vertex) [(99 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 80 = false := by
  rw [value20, value21, value24, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 142 = true ∨ valuation q 24 = true ∨ valuation q 80 = true := by
  rw [value20, value24, value80, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(168 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(168 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 20 = false ∨ valuation q 25 = false ∨ valuation q 29 = false := by
  rw [value20, value21, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (169 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 143 = true ∨ valuation q 20 = true ∨ valuation q 29 = true ∨ valuation q 81 = true := by
  rw [value20, value21, value29, value81, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(160 : Vertex), (177 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (169 : Vertex) [(160 : Vertex), (177 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 143 = true ∨ valuation q 20 = true ∨ valuation q 25 = true ∨ valuation q 81 = true := by
  rw [value20, value21, value25, value81, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (169 : Vertex), (417 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (177 : Vertex) [(160 : Vertex), (169 : Vertex), (417 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 33 = false ∨ valuation q 42 = false := by
  rw [value22, value23, value33, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (167 : Vertex) (182 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 33 = false ∨ valuation q 85 = false := by
  rw [value22, value23, value33, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (167 : Vertex) (182 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 42 = false ∨ valuation q 85 = false := by
  rw [value22, value23, value42, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (167 : Vertex) (230 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 33 = false ∨ valuation q 42 = false ∨ valuation q 85 = false := by
  rw [value22, value33, value42, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (182 : Vertex) (230 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 145 = true ∨ valuation q 28 = true ∨ valuation q 86 = true := by
  rw [value23, value28, value86, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(175 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (166 : Vertex) [(175 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 145 = true ∨ valuation q 22 = true ∨ valuation q 86 = true := by
  rw [value22, value23, value86, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(166 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (175 : Vertex) [(166 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 145 = true ∨ valuation q 22 = true ∨ valuation q 28 = true := by
  rw [value22, value23, value28, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(166 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (423 : Vertex) [(166 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 5 = false ∨ valuation q 20 = false ∨ valuation q 87 = false := by
  rw [value5, value20, value24, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (160 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 5 = false ∨ valuation q 25 = false ∨ valuation q 87 = false := by
  rw [value5, value24, value25, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (40 : Vertex) (169 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 146 = true ∨ valuation q 20 = true ∨ valuation q 25 = true ∨ valuation q 87 = true := by
  rw [value20, value24, value25, value87, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (40 : Vertex) → w ∈ [(160 : Vertex), (169 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (40 : Vertex) [(160 : Vertex), (169 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 146 = true ∨ valuation q 5 = true ∨ valuation q 25 = true ∨ valuation q 87 = true := by
  rw [value5, value24, value25, value87, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(40 : Vertex), (169 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (160 : Vertex) [(40 : Vertex), (169 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 146 = true ∨ valuation q 5 = true ∨ valuation q 20 = true ∨ valuation q 87 = true := by
  rw [value5, value20, value24, value87, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(40 : Vertex), (160 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (169 : Vertex) [(40 : Vertex), (160 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 146 = true ∨ valuation q 5 = true ∨ valuation q 20 = true ∨ valuation q 25 = true := by
  rw [value5, value20, value24, value25, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(40 : Vertex), (160 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (424 : Vertex) [(40 : Vertex), (160 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value21, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (168 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 27 = false := by
  rw [value21, value24, value25, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (168 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value21, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (161 : Vertex) (171 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value24, value25, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (171 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 7 = true ∨ valuation q 25 = true ∨ valuation q 28 = true ∨ valuation q 44 = true ∨ valuation q 89 = true := by
  rw [value7, value25, value26, value28, value44, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ∈ [(43 : Vertex), (169 : Vertex), (175 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (171 : Vertex) [(43 : Vertex), (169 : Vertex), (175 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 7 = false ∨ valuation q 25 = false ∨ valuation q 44 = false := by
  rw [value7, value25, value26, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (43 : Vertex) (169 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.First112
