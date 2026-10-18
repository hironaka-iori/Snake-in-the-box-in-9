import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 33 = false ∨ valuation q 39 = false := by
  rw [value33, value39, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (254 : Vertex) (238 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 140 = true ∨ valuation q 39 = true ∨ valuation q 41 = true := by
  rw [value39, value40, value41, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(252 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (238 : Vertex) [(252 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 141 = true ∨ valuation q 40 = true := by
  rw [value40, value41, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(254 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (239 : Vertex) [(254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 141 = true ∨ valuation q 34 = true := by
  rw [value34, value41, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(239 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (254 : Vertex) [(239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 1 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value1, value42, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (257 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 1 = false ∨ valuation q 43 = false ∨ valuation q 50 = false := by
  rw [value1, value42, value43, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (257 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 1 = false ∨ valuation q 46 = false ∨ valuation q 50 = false := by
  rw [value1, value42, value46, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (264 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 50 = false := by
  rw [value42, value43, value46, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (257 : Vertex) (264 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 143 = true ∨ valuation q 44 = true ∨ valuation q 47 = true := by
  rw [value43, value44, value47, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (256 : Vertex) → w ∈ [(261 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (256 : Vertex) [(261 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 143 = true ∨ valuation q 42 = true ∨ valuation q 47 = true := by
  rw [value42, value43, value47, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(256 : Vertex), (265 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (261 : Vertex) [(256 : Vertex), (265 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 144 = true ∨ valuation q 45 = true := by
  rw [value44, value45, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(263 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (257 : Vertex) [(263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 144 = true ∨ valuation q 43 = true := by
  rw [value43, value44, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(257 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (263 : Vertex) [(257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 145 = true ∨ valuation q 49 = true := by
  rw [value45, value49, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(271 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (261 : Vertex) [(271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 145 = true ∨ valuation q 44 = true := by
  rw [value44, value45, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (263 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (263 : Vertex) (271 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 146 = true ∨ valuation q 42 = true ∨ valuation q 71 = true := by
  rw [value42, value46, value71, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (264 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(256 : Vertex), (392 : Vertex)] := by decide
  have hg := other_cover q (264 : Vertex) (265 : Vertex) [(256 : Vertex), (392 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value43, value46, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (265 : Vertex) (257 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 147 = true ∨ valuation q 46 = true := by
  rw [value46, value47, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(264 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (257 : Vertex) [(264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 147 = true ∨ valuation q 43 = true := by
  rw [value43, value47, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(257 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (264 : Vertex) [(257 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 148 = true ∨ valuation q 56 = true := by
  rw [value48, value56, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(286 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (271 : Vertex) [(286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 148 = true ∨ valuation q 49 = true := by
  rw [value48, value49, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(271 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (286 : Vertex) [(271 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 149 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(270 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (263 : Vertex) [(270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 149 = true ∨ valuation q 45 = true := by
  rw [value45, value49, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(263 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (270 : Vertex) [(263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 53 = false := by
  rw [value42, value50, value51, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (256 : Vertex) (274 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 151 = true ∨ valuation q 50 = true := by
  rw [value50, value51, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(272 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (275 : Vertex) [(272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 152 = true ∨ valuation q 51 = true ∨ valuation q 54 = true := by
  rw [value51, value52, value54, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(274 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (19 : Vertex) [(274 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 152 = true ∨ valuation q 4 = true ∨ valuation q 51 = true := by
  rw [value4, value51, value52, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(19 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (283 : Vertex) [(19 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 153 = true ∨ valuation q 50 = true := by
  rw [value50, value53, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (284 : Vertex) [(272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 154 = true ∨ valuation q 75 = true := by
  rw [value54, value75, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(411 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (275 : Vertex) [(411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 155 = true ∨ valuation q 56 = true := by
  rw [value55, value56, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(286 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (276 : Vertex) [(286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 155 = true ∨ valuation q 53 = true := by
  rw [value53, value55, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (284 : Vertex) w → w ∈ region → w ≠ (286 : Vertex) → w ∈ [(276 : Vertex)] := by decide
  have hg := other_cover q (284 : Vertex) (286 : Vertex) [(276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 156 = true ∨ valuation q 55 = true := by
  rw [value55, value56, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(284 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (270 : Vertex) [(284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 156 = true ∨ valuation q 48 = true := by
  rw [value48, value56, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(270 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (284 : Vertex) [(270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E147.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112147
