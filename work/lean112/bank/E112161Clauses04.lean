import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 14 = false ∨ valuation q 30 = false ∨ valuation q 40 = false := by
  rw [value14, value30, value31, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (196 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 18 = false ∨ valuation q 37 = false ∨ valuation q 41 = false := by
  rw [value18, value32, value37, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (139 : Vertex) (219 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 143 = true ∨ valuation q 18 = true ∨ valuation q 41 = true := by
  rw [value18, value32, value41, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(139 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (219 : Vertex) [(139 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 143 = true ∨ valuation q 18 = true ∨ valuation q 37 = true := by
  rw [value18, value32, value37, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(139 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (235 : Vertex) [(139 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 34 = false := by
  rw [value20, value28, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (208 : Vertex) (144 : Vertex) (192 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 144 = true ∨ valuation q 20 = true ∨ valuation q 34 = true := by
  rw [value20, value33, value34, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(144 : Vertex), (209 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (192 : Vertex) [(144 : Vertex), (209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 144 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value20, value28, value33, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (208 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(144 : Vertex), (192 : Vertex)] := by decide
  have hg := other_cover q (208 : Vertex) (209 : Vertex) [(144 : Vertex), (192 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 145 = true ∨ valuation q 35 = true := by
  rw [value34, value35, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(211 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (208 : Vertex) [(211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 145 = true ∨ valuation q 33 = true := by
  rw [value33, value34, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(208 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (211 : Vertex) [(208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value34, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ∈ [(209 : Vertex), (215 : Vertex), (219 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (211 : Vertex) [(209 : Vertex), (215 : Vertex), (219 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 146 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value35, value36, value37, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(215 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (209 : Vertex) [(215 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 146 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value34, value35, value37, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(209 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (215 : Vertex) [(209 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 146 = true ∨ valuation q 34 = true ∨ valuation q 36 = true := by
  rw [value34, value35, value36, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (211 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(209 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (211 : Vertex) (219 : Vertex) [(209 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 147 = true ∨ valuation q 35 = true := by
  rw [value35, value36, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(211 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (151 : Vertex) [(211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 147 = true ∨ valuation q 24 = true := by
  rw [value24, value36, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(151 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (211 : Vertex) [(151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 148 = true ∨ valuation q 35 = true := by
  rw [value35, value37, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(211 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (203 : Vertex) [(211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 148 = true ∨ valuation q 32 = true := by
  rw [value32, value37, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(203 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (211 : Vertex) [(203 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 150 = true ∨ valuation q 41 = true := by
  rw [value39, value41, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(235 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (225 : Vertex) [(235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 150 = true ∨ valuation q 38 = true := by
  rw [value38, value39, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(225 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (235 : Vertex) [(225 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 31 = false ∨ valuation q 38 = false := by
  rw [value4, value31, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (197 : Vertex) (225 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 31 = false ∨ valuation q 99 = false := by
  rw [value4, value31, value40, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (197 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 4 = false ∨ valuation q 38 = false ∨ valuation q 99 = false := by
  rw [value4, value38, value40, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (229 : Vertex) (101 : Vertex) (225 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 42 = false := by
  rw [value32, value39, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (203 : Vertex) (227 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 101 = false := by
  rw [value32, value39, value41, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (203 : Vertex) (227 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 32 = false ∨ valuation q 42 = false ∨ valuation q 101 = false := by
  rw [value32, value41, value42, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (203 : Vertex) (239 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 101 = false := by
  rw [value39, value41, value42, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (239 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 152 = true ∨ valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 101 = true := by
  rw [value39, value41, value42, value101, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(227 : Vertex), (239 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (203 : Vertex) [(227 : Vertex), (239 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 152 = true ∨ valuation q 32 = true ∨ valuation q 39 = true ∨ valuation q 42 = true := by
  rw [value32, value39, value41, value42, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (491 : Vertex) → w ∈ [(203 : Vertex), (227 : Vertex), (239 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (491 : Vertex) [(203 : Vertex), (227 : Vertex), (239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 41 = true := by
  rw [value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ∈ [(235 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (239 : Vertex) [(235 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 153 = true := by
  rw [value42, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (239 : Vertex) (235 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 50 = false := by
  rw [value43, value45, value46, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 154 = true ∨ valuation q 45 = true ∨ valuation q 50 = true := by
  rw [value43, value45, value50, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(259 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(259 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E161.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112161
