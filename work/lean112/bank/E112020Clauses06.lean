import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 89 = true := by
  rw [value36, value37, value89, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (175 : Vertex) [(163 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 41 = true := by
  rw [value36, value37, value41, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (423 : Vertex) [(163 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 57 = false := by
  rw [value36, value38, value41, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (163 : Vertex) (175 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 162 = true ∨ valuation q 36 = true ∨ valuation q 57 = true := by
  rw [value36, value38, value57, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (175 : Vertex) [(163 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 58 = false := by
  rw [value39, value40, value49, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (172 : Vertex) (173 : Vertex) (188 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 163 = true ∨ valuation q 49 = true ∨ valuation q 58 = true := by
  rw [value39, value49, value58, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (172 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(188 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (172 : Vertex) (173 : Vertex) [(188 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 164 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (172 : Vertex) [(175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 164 = true ∨ valuation q 39 = true := by
  rw [value39, value40, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(172 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value37, value38, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (167 : Vertex) (171 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 165 = true ∨ valuation q 37 = true ∨ valuation q 38 = true := by
  rw [value37, value38, value41, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(167 : Vertex), (171 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [(167 : Vertex), (171 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 33 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value33, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 33 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value33, value42, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 33 = false ∨ valuation q 44 = false ∨ valuation q 46 = false := by
  rw [value33, value42, value44, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (180 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 46 = true := by
  rw [value42, value43, value44, value46, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(177 : Vertex), (180 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (160 : Vertex) [(177 : Vertex), (180 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 166 = true ∨ valuation q 33 = true ∨ valuation q 44 = true ∨ valuation q 46 = true := by
  rw [value33, value42, value44, value46, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (180 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (177 : Vertex) [(160 : Vertex), (180 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 34 = false ∨ valuation q 42 = false := by
  rw [value8, value34, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (161 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 34 = false ∨ valuation q 47 = false := by
  rw [value8, value34, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (161 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 34 = false ∨ valuation q 60 = false := by
  rw [value8, value34, value43, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (161 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 47 = false := by
  rw [value8, value42, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (176 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 60 = false := by
  rw [value8, value42, value43, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (176 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 8 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value8, value43, value47, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (49 : Vertex) (185 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 47 = false := by
  rw [value34, value42, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 60 = false := by
  rw [value34, value42, value43, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 34 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value34, value43, value47, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (185 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 42 = false ∨ valuation q 47 = false ∨ valuation q 60 = false := by
  rw [value42, value43, value47, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (176 : Vertex) (185 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 42 = false ∨ valuation q 45 = false := by
  rw [value9, value42, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value9, value42, value44, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (176 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 49 = false := by
  rw [value9, value44, value45, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 96 = false := by
  rw [value9, value44, value45, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (182 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 9 = false ∨ valuation q 49 = false ∨ valuation q 96 = false := by
  rw [value9, value44, value49, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (52 : Vertex) (188 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 49 = false := by
  rw [value42, value44, value45, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 96 = false := by
  rw [value42, value44, value45, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (176 : Vertex) (182 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E020.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112020
