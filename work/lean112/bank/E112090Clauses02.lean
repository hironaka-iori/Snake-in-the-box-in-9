import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 136 = true ∨ valuation q 25 = true ∨ valuation q 28 = true := by
  rw [value25, value27, value28, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(150 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (156 : Vertex) [(150 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 136 = true ∨ valuation q 25 = true ∨ valuation q 26 = true := by
  rw [value25, value26, value27, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(150 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(150 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 137 = true ∨ valuation q 27 = true := by
  rw [value27, value28, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (143 : Vertex) → w ∈ [(158 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (143 : Vertex) [(158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 137 = true ∨ valuation q 20 = true := by
  rw [value20, value28, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 138 = true ∨ valuation q 12 = true ∨ valuation q 30 = true := by
  rw [value12, value29, value30, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(130 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (198 : Vertex) [(130 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 13 = false ∨ valuation q 29 = false ∨ valuation q 39 = false := by
  rw [value13, value29, value30, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 140 = true := by
  rw [value31, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (196 : Vertex) (198 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 142 = true ∨ valuation q 19 = true ∨ valuation q 38 = true := by
  rw [value19, value33, value38, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(141 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (237 : Vertex) [(141 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 143 = true ∨ valuation q 22 = true := by
  rw [value22, value34, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(145 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (213 : Vertex) [(145 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 144 = true ∨ valuation q 34 = true ∨ valuation q 38 = true := by
  rw [value34, value35, value38, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(209 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (215 : Vertex) [(209 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 144 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value34, value35, value37, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(209 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (221 : Vertex) [(209 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 146 = true ∨ valuation q 36 = true := by
  rw [value36, value37, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 147 = true ∨ valuation q 35 = true := by
  rw [value35, value38, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (205 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 147 = true ∨ valuation q 33 = true := by
  rw [value33, value38, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(205 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (213 : Vertex) [(205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 30 = false ∨ valuation q 41 = false := by
  rw [value1, value30, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (195 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 30 = false ∨ valuation q 95 = false := by
  rw [value1, value30, value39, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (195 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 1 = false ∨ valuation q 41 = false ∨ valuation q 95 = false := by
  rw [value1, value39, value41, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (99 : Vertex) (231 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 30 = false ∨ valuation q 41 = false ∨ valuation q 95 = false := by
  rw [value30, value39, value41, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (195 : Vertex) (231 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 149 = true ∨ valuation q 43 = true := by
  rw [value40, value43, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(237 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (231 : Vertex) [(237 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 149 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (229 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [(231 : Vertex)] := by decide
  have hg := other_cover q (229 : Vertex) (237 : Vertex) [(231 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 150 = true ∨ valuation q 39 = true := by
  rw [value39, value41, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (231 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(227 : Vertex)] := by decide
  have hg := other_cover q (231 : Vertex) (229 : Vertex) [(227 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 151 = true := by
  rw [value42, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (237 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (233 : Vertex) (237 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 33 = false ∨ valuation q 40 = false ∨ valuation q 101 = false := by
  rw [value33, value40, value43, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (237 : Vertex) (205 : Vertex) (229 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 152 = true ∨ valuation q 33 = true ∨ valuation q 40 = true ∨ valuation q 42 = true := by
  rw [value33, value40, value42, value43, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (237 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(205 : Vertex), (229 : Vertex), (233 : Vertex)] := by decide
  have hg := other_cover q (237 : Vertex) (493 : Vertex) [(205 : Vertex), (229 : Vertex), (233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value44, value45, value46, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 54 = false := by
  rw [value44, value45, value46, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 48 = false ∨ valuation q 54 = false := by
  rw [value44, value45, value48, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (265 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 54 = false := by
  rw [value44, value46, value48, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (261 : Vertex) (265 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 153 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value44, value45, value48, value54, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(259 : Vertex), (265 : Vertex), (273 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(259 : Vertex), (265 : Vertex), (273 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 155 = true ∨ valuation q 47 = true ∨ valuation q 51 = true := by
  rw [value46, value47, value51, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(263 : Vertex), (269 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(263 : Vertex), (269 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 155 = true ∨ valuation q 44 = true ∨ valuation q 51 = true := by
  rw [value44, value46, value51, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(257 : Vertex), (269 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (263 : Vertex) [(257 : Vertex), (269 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 155 = true ∨ valuation q 44 = true ∨ valuation q 47 = true := by
  rw [value44, value46, value47, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(257 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (269 : Vertex) [(257 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E090.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112090
