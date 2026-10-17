import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 11 = false ∨ valuation q 24 = false ∨ valuation q 41 = false := by
  rw [value11, value22, value24, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (182 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 41 = false := by
  rw [value15, value22, value24, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (164 : Vertex) (182 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 145 = true ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 23 = true ∨ valuation q 41 = true := by
  rw [value11, value15, value22, value23, value41, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (180 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(52 : Vertex), (164 : Vertex), (181 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (180 : Vertex) (182 : Vertex) [(52 : Vertex), (164 : Vertex), (181 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value21, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (177 : Vertex) (180 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 146 = true ∨ valuation q 22 = true ∨ valuation q 25 = true := by
  rw [value22, value23, value25, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(180 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (177 : Vertex) [(180 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 146 = true ∨ valuation q 21 = true ∨ valuation q 22 = true := by
  rw [value21, value22, value23, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (181 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(177 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (181 : Vertex) (183 : Vertex) [(177 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 95 = false := by
  rw [value22, value24, value25, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (180 : Vertex) (183 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 147 = true ∨ valuation q 22 = true ∨ valuation q 95 = true := by
  rw [value22, value24, value95, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(180 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (183 : Vertex) [(180 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 147 = true ∨ valuation q 22 = true ∨ valuation q 25 = true := by
  rw [value22, value24, value25, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(180 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (438 : Vertex) [(180 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 16 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value16, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (183 : Vertex) (167 : Vertex) (181 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 148 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value23, value24, value25, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (167 : Vertex) → w ∈ [(181 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (167 : Vertex) [(181 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 148 = true ∨ valuation q 16 = true ∨ valuation q 24 = true := by
  rw [value16, value24, value25, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(167 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (181 : Vertex) [(167 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 148 = true ∨ valuation q 16 = true ∨ valuation q 23 = true := by
  rw [value16, value23, value25, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (183 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(167 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (183 : Vertex) (182 : Vertex) [(167 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 149 = true ∨ valuation q 28 = true := by
  rw [value26, value28, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(187 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (177 : Vertex) [(187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 149 = true ∨ valuation q 21 = true := by
  rw [value21, value26, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(177 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (187 : Vertex) [(177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 43 = false := by
  rw [value18, value27, value28, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (170 : Vertex) (187 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 151 = true ∨ valuation q 26 = true ∨ valuation q 27 = true := by
  rw [value26, value27, value28, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(185 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (171 : Vertex) [(185 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 151 = true ∨ valuation q 19 = true ∨ valuation q 27 = true := by
  rw [value19, value27, value28, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(171 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (185 : Vertex) [(171 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 151 = true ∨ valuation q 19 = true ∨ valuation q 26 = true := by
  rw [value19, value26, value28, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(171 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (186 : Vertex) [(171 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value29, value30, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (227 : Vertex) (229 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 102 = false := by
  rw [value29, value30, value31, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (227 : Vertex) (229 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 35 = false ∨ valuation q 102 = false := by
  rw [value29, value30, value35, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (227 : Vertex) (233 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 152 = true ∨ valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 102 = true := by
  rw [value29, value31, value35, value102, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(229 : Vertex), (233 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (227 : Vertex) [(229 : Vertex), (233 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 152 = true ∨ valuation q 30 = true ∨ valuation q 35 = true ∨ valuation q 102 = true := by
  rw [value29, value30, value35, value102, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(227 : Vertex), (233 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (229 : Vertex) [(227 : Vertex), (233 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 152 = true ∨ valuation q 30 = true ∨ valuation q 31 = true ∨ valuation q 102 = true := by
  rw [value29, value30, value31, value102, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(227 : Vertex), (229 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (233 : Vertex) [(227 : Vertex), (229 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 152 = true ∨ valuation q 30 = true ∨ valuation q 31 = true ∨ valuation q 35 = true := by
  rw [value29, value30, value31, value35, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(227 : Vertex), (229 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (481 : Vertex) [(227 : Vertex), (229 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 40 = false := by
  rw [value29, value30, value33, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (225 : Vertex) (231 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 153 = true ∨ valuation q 33 = true ∨ valuation q 40 = true := by
  rw [value30, value33, value40, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(231 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (225 : Vertex) [(231 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 105 = false := by
  rw [value29, value31, value33, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (225 : Vertex) (231 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 154 = true ∨ valuation q 33 = true ∨ valuation q 105 = true := by
  rw [value31, value33, value105, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(231 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (225 : Vertex) [(231 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 106 = false := by
  rw [value32, value33, value36, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (230 : Vertex) (231 : Vertex) (238 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 36 = false ∨ valuation q 106 = false := by
  rw [value36, value106, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (230 : Vertex) (238 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E097.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112097
