import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 149 = true ∨ valuation q 36 = true := by
  rw [value36, value39, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(210 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (222 : Vertex) [(210 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 150 = true ∨ valuation q 41 = true := by
  rw [value40, value41, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 1 = false ∨ valuation q 45 = false ∨ valuation q 62 = false := by
  rw [value1, value43, value45, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (0 : Vertex) (260 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 62 = false := by
  rw [value43, value44, value45, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (258 : Vertex) (260 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 62 = false := by
  rw [value43, value45, value53, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (256 : Vertex) (260 : Vertex) (272 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 154 = true ∨ valuation q 43 = true ∨ valuation q 46 = true := by
  rw [value43, value44, value46, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(256 : Vertex), (262 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(256 : Vertex), (262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 54 = false := by
  rw [value43, value45, value46, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (262 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value43, value45, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (256 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value45, value46, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 66 = false := by
  rw [value46, value47, value56, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (263 : Vertex) (262 : Vertex) (279 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 43 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value43, value48, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (265 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 43 = false ∨ valuation q 49 = false ∨ valuation q 67 = false := by
  rw [value43, value48, value49, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (265 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 43 = false ∨ valuation q 50 = false ∨ valuation q 67 = false := by
  rw [value43, value48, value50, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (266 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 43 = false ∨ valuation q 51 = false ∨ valuation q 67 = false := by
  rw [value43, value48, value51, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (256 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value48, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (265 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 67 = false := by
  rw [value48, value49, value50, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (265 : Vertex) (266 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 67 = false := by
  rw [value48, value49, value51, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (264 : Vertex) (265 : Vertex) (268 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 57 = false := by
  rw [value3, value48, value49, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (9 : Vertex) (264 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 159 = true ∨ valuation q 48 = true ∨ valuation q 57 = true ∨ valuation q 68 = true := by
  rw [value48, value49, value57, value68, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (9 : Vertex) → w ∈ [(264 : Vertex), (281 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (9 : Vertex) [(264 : Vertex), (281 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 159 = true ∨ valuation q 3 = true ∨ valuation q 57 = true ∨ valuation q 68 = true := by
  rw [value3, value49, value57, value68, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(9 : Vertex), (281 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (264 : Vertex) [(9 : Vertex), (281 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 160 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 58 = true := by
  rw [value48, value50, value52, value58, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(264 : Vertex), (270 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(264 : Vertex), (270 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 160 = true ∨ valuation q 44 = true ∨ valuation q 48 = true ∨ valuation q 58 = true := by
  rw [value44, value48, value50, value58, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex), (264 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (270 : Vertex) [(258 : Vertex), (264 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value45, value48, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ∈ [(260 : Vertex), (264 : Vertex), (270 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (268 : Vertex) [(260 : Vertex), (264 : Vertex), (270 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 161 = true ∨ valuation q 45 = true ∨ valuation q 48 = true := by
  rw [value45, value48, value51, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (264 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (264 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 46 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value46, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 6 = false ∨ valuation q 43 = false ∨ valuation q 54 = false := by
  rw [value6, value43, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (16 : Vertex) (256 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 163 = true ∨ valuation q 43 = true ∨ valuation q 54 = true := by
  rw [value43, value53, value54, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(256 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (16 : Vertex) [(256 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 163 = true ∨ valuation q 6 = true ∨ valuation q 43 = true := by
  rw [value6, value43, value53, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(16 : Vertex), (256 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(16 : Vertex), (256 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 164 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value53, value54, value55, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(272 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (260 : Vertex) [(272 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 164 = true ∨ valuation q 45 = true ∨ valuation q 55 = true := by
  rw [value45, value54, value55, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(260 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(260 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 164 = true ∨ valuation q 45 = true ∨ valuation q 53 = true := by
  rw [value45, value53, value54, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 60 = false := by
  rw [value54, value55, value56, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (276 : Vertex) (279 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E107.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112107
