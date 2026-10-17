import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 155 = true ∨ valuation q 10 = true ∨ valuation q 33 = true ∨ valuation q 38 = true ∨ valuation q 45 = true := by
  rw [value10, value33, value37, value38, value45, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(72 : Vertex), (192 : Vertex), (201 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (204 : Vertex) [(72 : Vertex), (192 : Vertex), (201 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value20, value34, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 46 = false := by
  rw [value20, value34, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 104 = false := by
  rw [value20, value34, value38, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 20 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value20, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 20 = false ∨ valuation q 37 = false ∨ valuation q 104 = false := by
  rw [value20, value37, value38, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 46 = false := by
  rw [value34, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 37 = true := by
  rw [value37, value39, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(200 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (206 : Vertex) [(200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 39 = true := by
  rw [value39, value40, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(204 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (198 : Vertex) [(204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 158 = true ∨ valuation q 35 = true := by
  rw [value35, value40, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (206 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(198 : Vertex)] := by decide
  have hg := other_cover q (206 : Vertex) (204 : Vertex) [(198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 26 = false ∨ valuation q 43 = false := by
  rw [value12, value26, value41, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 26 = false ∨ valuation q 47 = false := by
  rw [value12, value26, value41, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 26 = false ∨ valuation q 111 = false := by
  rw [value12, value26, value41, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (146 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value12, value41, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 12 = false ∨ valuation q 47 = false ∨ valuation q 111 = false := by
  rw [value12, value41, value47, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (82 : Vertex) (218 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 26 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value26, value41, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (146 : Vertex) (214 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 26 = false ∨ valuation q 47 = false ∨ valuation q 111 = false := by
  rw [value26, value41, value47, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (146 : Vertex) (218 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 12 = true ∨ valuation q 26 = true ∨ valuation q 47 = true ∨ valuation q 111 = true := by
  rw [value12, value26, value41, value47, value111, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(82 : Vertex), (146 : Vertex), (218 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (214 : Vertex) [(82 : Vertex), (146 : Vertex), (218 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 49 = true := by
  rw [value42, value49, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (215 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 160 = true ∨ valuation q 44 = true := by
  rw [value42, value44, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (221 : Vertex) [(215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value35, value41, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (210 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 114 = false := by
  rw [value35, value43, value44, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (214 : Vertex) (198 : Vertex) (215 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 161 = true ∨ valuation q 35 = true ∨ valuation q 44 = true ∨ valuation q 114 = true := by
  rw [value35, value43, value44, value114, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (210 : Vertex) → w ∈ [(198 : Vertex), (215 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (210 : Vertex) [(198 : Vertex), (215 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 36 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value36, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (215 : Vertex) (199 : Vertex) (213 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value37, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 115 = false := by
  rw [value37, value45, value46, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (217 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 115 = false := by
  rw [value37, value45, value47, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (200 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 38 = true ∨ valuation q 45 = true ∨ valuation q 49 = true := by
  rw [value38, value45, value46, value49, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(201 : Vertex), (216 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (219 : Vertex) [(201 : Vertex), (216 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 38 = true ∨ valuation q 45 = true ∨ valuation q 48 = true := by
  rw [value38, value45, value46, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(201 : Vertex), (216 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (221 : Vertex) [(201 : Vertex), (216 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 47 = true := by
  rw [value47, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (218 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 29 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value29, value41, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 29 = false ∨ valuation q 41 = false ∨ valuation q 48 = false := by
  rw [value29, value41, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (154 : Vertex) (210 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E047.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112047
