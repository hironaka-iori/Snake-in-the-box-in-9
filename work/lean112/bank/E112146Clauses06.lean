import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 38 = false ∨ valuation q 54 = false ∨ valuation q 89 = false := by
  rw [value38, value39, value54, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (145 : Vertex) (144 : Vertex) (209 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 154 = true ∨ valuation q 38 = true := by
  rw [value38, value40, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (130 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 154 = true ∨ valuation q 29 = true := by
  rw [value29, value40, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(130 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(130 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 155 = true ∨ valuation q 42 = true := by
  rw [value41, value42, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (144 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 155 = true ∨ valuation q 38 = true := by
  rw [value38, value41, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(144 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (156 : Vertex) [(144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = true ∨ valuation q 41 = true ∨ valuation q 43 = true := by
  rw [value35, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ∈ [(140 : Vertex), (148 : Vertex), (158 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (156 : Vertex) [(140 : Vertex), (148 : Vertex), (158 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value35, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (140 : Vertex) (148 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 156 = true ∨ valuation q 35 = true ∨ valuation q 43 = true := by
  rw [value35, value42, value43, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(140 : Vertex), (158 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (148 : Vertex) [(140 : Vertex), (158 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 156 = true ∨ valuation q 35 = true ∨ valuation q 41 = true := by
  rw [value35, value41, value42, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (156 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(140 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (156 : Vertex) (158 : Vertex) [(140 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 157 = true ∨ valuation q 44 = true := by
  rw [value43, value44, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(159 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (156 : Vertex) [(159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 157 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (158 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (158 : Vertex) (159 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 158 = true ∨ valuation q 37 = true := by
  rw [value37, value44, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (158 : Vertex) → w ∈ [(143 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (158 : Vertex) [(143 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 159 = true ∨ valuation q 46 = true := by
  rw [value45, value46, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(194 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (196 : Vertex) [(194 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 29 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value29, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (192 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 29 = false ∨ valuation q 45 = false ∨ valuation q 50 = false := by
  rw [value29, value45, value46, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (192 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 29 = false ∨ valuation q 47 = false ∨ valuation q 49 = false := by
  rw [value29, value46, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (195 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 29 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value29, value46, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (194 : Vertex) (130 : Vertex) (198 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 30 = false ∨ valuation q 51 = false := by
  rw [value9, value30, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (131 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 9 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value9, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (67 : Vertex) (194 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 30 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value30, value46, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (131 : Vertex) (194 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 162 = true ∨ valuation q 49 = true ∨ valuation q 52 = true := by
  rw [value48, value49, value52, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(198 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (192 : Vertex) [(198 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 162 = true ∨ valuation q 45 = true ∨ valuation q 52 = true := by
  rw [value45, value48, value52, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(192 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (198 : Vertex) [(192 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 162 = true ∨ valuation q 45 = true ∨ valuation q 49 = true := by
  rw [value45, value48, value49, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(192 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (204 : Vertex) [(192 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value46, value48, value49, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (196 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 163 = true ∨ valuation q 46 = true ∨ valuation q 48 = true := by
  rw [value46, value48, value49, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (214 : Vertex) [(194 : Vertex), (196 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 46 = false ∨ valuation q 51 = false := by
  rw [value13, value46, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (194 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 51 = false ∨ valuation q 60 = false := by
  rw [value13, value50, value51, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (74 : Vertex) (203 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 60 = false := by
  rw [value46, value50, value51, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (203 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value14, value47, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (203 : Vertex) (75 : Vertex) (195 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 165 = true ∨ valuation q 34 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value34, value47, value50, value51, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(139 : Vertex), (195 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (75 : Vertex) [(139 : Vertex), (195 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 165 = true ∨ valuation q 14 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value14, value47, value50, value51, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (139 : Vertex) → w ∈ [(75 : Vertex), (195 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (139 : Vertex) [(75 : Vertex), (195 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 165 = true ∨ valuation q 14 = true ∨ valuation q 34 = true ∨ valuation q 50 = true := by
  rw [value14, value34, value50, value51, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (195 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (195 : Vertex) [(75 : Vertex), (139 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E146.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112146
