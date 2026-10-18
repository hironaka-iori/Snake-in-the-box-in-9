import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 17 = false ∨ valuation q 40 = false ∨ valuation q 103 = false := by
  rw [value17, value37, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (168 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 17 = false ∨ valuation q 46 = false ∨ valuation q 103 = false := by
  rw [value17, value37, value46, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (168 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 31 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value31, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 31 = false ∨ valuation q 38 = false ∨ valuation q 46 = false := by
  rw [value31, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (234 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 31 = false ∨ valuation q 38 = false ∨ valuation q 103 = false := by
  rw [value31, value37, value38, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (234 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 31 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value31, value37, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 31 = false ∨ valuation q 40 = false ∨ valuation q 103 = false := by
  rw [value31, value37, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 31 = false ∨ valuation q 46 = false ∨ valuation q 103 = false := by
  rw [value31, value37, value46, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (224 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value37, value38, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (234 : Vertex) (236 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 103 = false := by
  rw [value37, value38, value40, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (234 : Vertex) (236 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 103 = false := by
  rw [value37, value38, value46, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (234 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 46 = false ∨ valuation q 103 = false := by
  rw [value37, value40, value46, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (236 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 17 = true ∨ valuation q 31 = true ∨ valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 46 = true ∨ valuation q 103 = true := by
  rw [value17, value31, value37, value38, value40, value46, value103, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(168 : Vertex), (224 : Vertex), (234 : Vertex), (236 : Vertex), (248 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (104 : Vertex) [(168 : Vertex), (224 : Vertex), (234 : Vertex), (236 : Vertex), (248 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 9 = true ∨ valuation q 17 = true ∨ valuation q 31 = true ∨ valuation q 40 = true ∨ valuation q 46 = true ∨ valuation q 103 = true := by
  rw [value9, value17, value31, value37, value40, value46, value103, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(104 : Vertex), (168 : Vertex), (224 : Vertex), (236 : Vertex), (248 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (234 : Vertex) [(104 : Vertex), (168 : Vertex), (224 : Vertex), (236 : Vertex), (248 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 9 = true ∨ valuation q 17 = true ∨ valuation q 31 = true ∨ valuation q 38 = true ∨ valuation q 46 = true ∨ valuation q 103 = true := by
  rw [value9, value17, value31, value37, value38, value46, value103, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(104 : Vertex), (168 : Vertex), (224 : Vertex), (234 : Vertex), (248 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (236 : Vertex) [(104 : Vertex), (168 : Vertex), (224 : Vertex), (234 : Vertex), (248 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 48 = false := by
  rw [value33, value37, value38, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (226 : Vertex) (232 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 48 = false := by
  rw [value37, value38, value39, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (232 : Vertex) (235 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 48 = false := by
  rw [value37, value38, value41, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (234 : Vertex) (232 : Vertex) (238 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 48 = true := by
  rw [value37, value38, value39, value41, value48, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(232 : Vertex), (235 : Vertex), (238 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (226 : Vertex) [(232 : Vertex), (235 : Vertex), (238 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 48 = true := by
  rw [value33, value37, value38, value39, value48, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (234 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(226 : Vertex), (232 : Vertex), (235 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (234 : Vertex) (238 : Vertex) [(226 : Vertex), (232 : Vertex), (235 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 18 = false ∨ valuation q 38 = false ∨ valuation q 49 = false := by
  rw [value18, value38, value39, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 18 = false ∨ valuation q 38 = false ∨ valuation q 105 = false := by
  rw [value18, value38, value39, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (234 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 18 = false ∨ valuation q 49 = false ∨ valuation q 105 = false := by
  rw [value18, value39, value49, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (171 : Vertex) (251 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 38 = true ∨ valuation q 49 = true ∨ valuation q 105 = true := by
  rw [value38, value39, value49, value105, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(234 : Vertex), (251 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (171 : Vertex) [(234 : Vertex), (251 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 40 = true := by
  rw [value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (236 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value34, value37, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ∈ [(228 : Vertex), (232 : Vertex), (238 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (236 : Vertex) [(228 : Vertex), (232 : Vertex), (238 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 37 = true ∨ valuation q 41 = true := by
  rw [value37, value40, value41, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(232 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(232 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 34 = true ∨ valuation q 41 = true := by
  rw [value34, value40, value41, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(228 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (232 : Vertex) [(228 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value34, value37, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(228 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (238 : Vertex) [(228 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value36, value38, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (230 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 157 = true ∨ valuation q 38 = true ∨ valuation q 40 = true := by
  rw [value38, value40, value41, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(234 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (230 : Vertex) [(234 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 157 = true ∨ valuation q 36 = true ∨ valuation q 40 = true := by
  rw [value36, value40, value41, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(230 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (234 : Vertex) [(230 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E169.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112169
