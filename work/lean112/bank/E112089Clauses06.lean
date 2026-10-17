import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 75 = true := by
  rw [value32, value33, value75, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(88 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (91 : Vertex) [(88 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value32, value33, value34, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(88 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (218 : Vertex) [(88 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 34 = true := by
  rw [value34, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (91 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value28, value33, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (91 : Vertex) (83 : Vertex) (90 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 28 = false ∨ valuation q 33 = false := by
  rw [value28, value33, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (91 : Vertex) (83 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value33, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (91 : Vertex) (90 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 33 = true ∨ valuation q 35 = true := by
  rw [value33, value34, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(90 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (83 : Vertex) [(90 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 28 = true ∨ valuation q 35 = true := by
  rw [value28, value34, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(83 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (90 : Vertex) [(83 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 158 = true ∨ valuation q 28 = true ∨ valuation q 33 = true := by
  rw [value28, value33, value34, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(83 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (95 : Vertex) [(83 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 34 = false := by
  rw [value27, value31, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (79 : Vertex) (87 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 31 = true ∨ valuation q 34 = true := by
  rw [value31, value34, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(87 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (79 : Vertex) [(87 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 34 = true := by
  rw [value27, value34, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(79 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (87 : Vertex) [(79 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 159 = true ∨ valuation q 27 = true ∨ valuation q 31 = true := by
  rw [value27, value31, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(79 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (91 : Vertex) [(79 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 2 = false ∨ valuation q 41 = false ∨ valuation q 46 = false := by
  rw [value2, value36, value41, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (1 : Vertex) (137 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 46 = false ∨ valuation q 56 = false := by
  rw [value36, value41, value46, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (129 : Vertex) (137 : Vertex) (145 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 57 = false := by
  rw [value37, value39, value42, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 91 = false := by
  rw [value37, value39, value42, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 57 = false ∨ valuation q 91 = false := by
  rw [value37, value39, value57, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (134 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 42 = false ∨ valuation q 57 = false ∨ valuation q 91 = false := by
  rw [value37, value42, value57, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (130 : Vertex) (138 : Vertex) (194 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 42 = true ∨ valuation q 57 = true ∨ valuation q 91 = true := by
  rw [value37, value42, value57, value91, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(138 : Vertex), (194 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (134 : Vertex) [(138 : Vertex), (194 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 47 = false := by
  rw [value38, value39, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (134 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 44 = true ∨ valuation q 47 = true := by
  rw [value38, value44, value47, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(140 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (134 : Vertex) [(140 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 39 = true ∨ valuation q 47 = true := by
  rw [value38, value39, value47, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(134 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (140 : Vertex) [(134 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 39 = true ∨ valuation q 44 = true := by
  rw [value38, value39, value44, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(134 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (148 : Vertex) [(134 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 39 = true := by
  rw [value39, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (134 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value37, value38, value39, value49, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ∈ [(130 : Vertex), (132 : Vertex), (150 : Vertex), (198 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (134 : Vertex) [(130 : Vertex), (132 : Vertex), (150 : Vertex), (198 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 49 = false := by
  rw [value37, value38, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 38 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value38, value39, value49, value60, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(132 : Vertex), (150 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (130 : Vertex) [(132 : Vertex), (150 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 37 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value37, value39, value49, value60, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(130 : Vertex), (150 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (132 : Vertex) [(130 : Vertex), (150 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 60 = true := by
  rw [value37, value38, value39, value60, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (150 : Vertex) [(130 : Vertex), (132 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 49 = true := by
  rw [value37, value38, value39, value49, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (198 : Vertex) [(130 : Vertex), (132 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 44 = false := by
  rw [value40, value41, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E089.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112089
