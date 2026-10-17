import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 57 = false := by
  rw [value31, value35, value39, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (177 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 160 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(189 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value38, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (181 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 99 = false := by
  rw [value43, value44, value46, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (227 : Vertex) (229 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 44 = false ∨ valuation q 99 = false := by
  rw [value44, value99, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (225 : Vertex) (227 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 163 = true ∨ valuation q 46 = true ∨ valuation q 99 = true := by
  rw [value43, value46, value99, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(229 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (227 : Vertex) [(229 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 164 = true ∨ valuation q 49 = true ∨ valuation q 101 = true := by
  rw [value44, value49, value101, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(235 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (225 : Vertex) [(235 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 164 = true ∨ valuation q 43 = true ∨ valuation q 101 = true := by
  rw [value43, value44, value101, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(225 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (235 : Vertex) [(225 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value45, value46, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 53 = false := by
  rw [value45, value46, value47, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value45, value46, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value45, value47, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 102 = false := by
  rw [value43, value45, value46, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (225 : Vertex) (228 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value43, value46, value51, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (225 : Vertex) (237 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 167 = true ∨ valuation q 12 = true ∨ valuation q 28 = true ∨ valuation q 45 = true ∨ valuation q 103 = true := by
  rw [value12, value28, value45, value47, value103, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(102 : Vertex), (166 : Vertex), (228 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (246 : Vertex) [(102 : Vertex), (166 : Vertex), (228 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 167 = true ∨ valuation q 12 = true ∨ valuation q 28 = true ∨ valuation q 45 = true ∨ valuation q 54 = true := by
  rw [value12, value28, value45, value47, value54, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(102 : Vertex), (166 : Vertex), (228 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (486 : Vertex) [(102 : Vertex), (166 : Vertex), (228 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 49 = true ∨ valuation q 58 = true ∨ valuation q 105 = true := by
  rw [value48, value49, value58, value105, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(235 : Vertex), (250 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (170 : Vertex) [(235 : Vertex), (250 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 32 = true ∨ valuation q 58 = true ∨ valuation q 105 = true := by
  rw [value32, value48, value58, value105, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(170 : Vertex), (250 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (235 : Vertex) [(170 : Vertex), (250 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 168 = true ∨ valuation q 32 = true ∨ valuation q 49 = true ∨ valuation q 58 = true := by
  rw [value32, value48, value49, value58, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(170 : Vertex), (235 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (490 : Vertex) [(170 : Vertex), (235 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 44 = false ∨ valuation q 48 = false ∨ valuation q 59 = false := by
  rw [value44, value48, value49, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 170 = true ∨ valuation q 51 = true ∨ valuation q 106 = true := by
  rw [value50, value51, value106, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(237 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(237 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 170 = true ∨ valuation q 45 = true ∨ valuation q 106 = true := by
  rw [value45, value50, value106, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(228 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (237 : Vertex) [(228 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 170 = true ∨ valuation q 45 = true ∨ valuation q 51 = true := by
  rw [value45, value50, value51, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(228 : Vertex), (237 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (492 : Vertex) [(228 : Vertex), (237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 172 = true ∨ valuation q 53 = true := by
  rw [value52, value53, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(244 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (248 : Vertex) [(244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 45 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value45, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (228 : Vertex) (240 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 173 = true ∨ valuation q 45 = true ∨ valuation q 54 = true := by
  rw [value45, value53, value54, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(228 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (240 : Vertex) [(228 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value47, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (230 : Vertex) (244 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 114 = false := by
  rw [value47, value53, value54, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (230 : Vertex) (244 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 114 = false := by
  rw [value53, value54, value55, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (246 : Vertex) (244 : Vertex) (247 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 175 = true ∨ valuation q 60 = true ∨ valuation q 115 = true := by
  rw [value55, value60, value115, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(255 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (246 : Vertex) [(255 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 175 = true ∨ valuation q 54 = true ∨ valuation q 115 = true := by
  rw [value54, value55, value115, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(246 : Vertex), (503 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(246 : Vertex), (503 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 176 = true ∨ valuation q 57 = true ∨ valuation q 58 = true := by
  rw [value56, value57, value58, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (240 : Vertex) [(249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E152.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112152
