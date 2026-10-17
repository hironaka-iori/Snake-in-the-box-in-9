import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 134 = true ∨ valuation q 26 = true := by
  rw [value25, value26, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(187 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (170 : Vertex) [(187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 134 = true ∨ valuation q 16 = true := by
  rw [value16, value25, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(170 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (187 : Vertex) [(170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 137 = true ∨ valuation q 31 = true := by
  rw [value28, value31, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (194 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(202 : Vertex)] := by decide
  have hg := other_cover q (194 : Vertex) (192 : Vertex) [(202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 29 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value29, value30, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (196 : Vertex) (205 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 28 = false ∨ valuation q 32 = false ∨ valuation q 40 = false := by
  rw [value28, value31, value32, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (203 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 141 = true ∨ valuation q 41 = true := by
  rw [value32, value41, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(219 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (202 : Vertex) [(219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 141 = true ∨ valuation q 31 = true := by
  rw [value31, value32, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(202 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (219 : Vertex) [(202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 143 = true ∨ valuation q 30 = true ∨ valuation q 95 = true := by
  rw [value30, value34, value95, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(197 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (204 : Vertex) [(197 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 146 = true ∨ valuation q 42 = true := by
  rw [value37, value42, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(222 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (215 : Vertex) [(222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 148 = true ∨ valuation q 41 = true := by
  rw [value39, value41, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (209 : Vertex) [(219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 31 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value31, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (202 : Vertex) (219 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value32, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 98 = false := by
  rw [value37, value40, value42, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 151 = true ∨ valuation q 40 = true ∨ valuation q 98 = true := by
  rw [value40, value42, value98, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(218 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (214 : Vertex) [(218 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 43 = true := by
  rw [value43, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (257 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 52 = false := by
  rw [value43, value44, value45, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (257 : Vertex) (259 : Vertex) (261 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 152 = true ∨ valuation q 45 = true ∨ valuation q 52 = true := by
  rw [value43, value45, value52, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(261 : Vertex), (273 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (259 : Vertex) [(261 : Vertex), (273 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 152 = true ∨ valuation q 44 = true ∨ valuation q 52 = true := by
  rw [value43, value44, value52, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(259 : Vertex), (273 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(259 : Vertex), (273 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 153 = true ∨ valuation q 46 = true ∨ valuation q 54 = true := by
  rw [value44, value46, value54, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(267 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (257 : Vertex) [(267 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 153 = true ∨ valuation q 43 = true ∨ valuation q 54 = true := by
  rw [value43, value44, value54, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(257 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(257 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 153 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value44, value46, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(257 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (275 : Vertex) [(257 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 43 = false ∨ valuation q 48 = false := by
  rw [value1, value43, value45, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (257 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 1 = false ∨ valuation q 43 = false ∨ valuation q 64 = false := by
  rw [value1, value43, value45, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (5 : Vertex) (257 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 154 = true ∨ valuation q 43 = true ∨ valuation q 48 = true ∨ valuation q 64 = true := by
  rw [value43, value45, value48, value64, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(257 : Vertex), (269 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (5 : Vertex) [(257 : Vertex), (269 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 154 = true ∨ valuation q 1 = true ∨ valuation q 48 = true ∨ valuation q 64 = true := by
  rw [value1, value45, value48, value64, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(5 : Vertex), (269 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(5 : Vertex), (269 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 44 = false ∨ valuation q 50 = false := by
  rw [value2, value44, value46, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 44 = false ∨ valuation q 66 = false := by
  rw [value2, value44, value46, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 2 = false ∨ valuation q 50 = false ∨ valuation q 66 = false := by
  rw [value2, value46, value50, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (271 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 44 = false ∨ valuation q 50 = false ∨ valuation q 66 = false := by
  rw [value44, value46, value50, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (271 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 2 = false ∨ valuation q 50 = false := by
  rw [value2, value50, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (267 : Vertex) (11 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 155 = true ∨ valuation q 44 = true ∨ valuation q 50 = true ∨ valuation q 66 = true := by
  rw [value44, value46, value50, value66, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(259 : Vertex), (271 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (11 : Vertex) [(259 : Vertex), (271 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 156 = true ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 67 = true := by
  rw [value47, value48, value49, value67, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(269 : Vertex), (270 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (284 : Vertex) [(269 : Vertex), (270 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E166.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112166
