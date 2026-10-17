import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value38, value39, value40, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (214 : Vertex) (218 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 48 = true ∨ valuation q 78 = true := by
  rw [value43, value48, value78, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(266 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (259 : Vertex) [(266 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 44 = true ∨ valuation q 78 = true := by
  rw [value43, value44, value78, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(259 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(259 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 49 = true ∨ valuation q 79 = true := by
  rw [value44, value49, value79, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(267 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(267 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 43 = true ∨ valuation q 79 = true := by
  rw [value43, value44, value79, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(258 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(258 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 43 = true ∨ valuation q 49 = true := by
  rw [value43, value44, value49, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (387 : Vertex) [(258 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value45, value46, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 54 = true ∨ valuation q 80 = true := by
  rw [value46, value54, value80, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(277 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (260 : Vertex) [(277 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 162 = true ∨ valuation q 45 = true ∨ valuation q 80 = true := by
  rw [value45, value46, value80, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (277 : Vertex) [(260 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 49 = true ∨ valuation q 65 = true ∨ valuation q 82 = true := by
  rw [value47, value49, value65, value82, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(267 : Vertex), (329 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (281 : Vertex) [(267 : Vertex), (329 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 82 = true := by
  rw [value47, value49, value57, value82, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(267 : Vertex), (281 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (329 : Vertex) [(267 : Vertex), (281 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 49 = true ∨ valuation q 57 = true ∨ valuation q 65 = true := by
  rw [value47, value49, value57, value65, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(267 : Vertex), (281 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (393 : Vertex) [(267 : Vertex), (281 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 58 = true ∨ valuation q 83 = true := by
  rw [value48, value49, value51, value58, value83, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(267 : Vertex), (270 : Vertex), (282 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(267 : Vertex), (270 : Vertex), (282 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 43 = true ∨ valuation q 49 = true ∨ valuation q 58 = true ∨ valuation q 83 = true := by
  rw [value43, value48, value49, value58, value83, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex), (282 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (270 : Vertex) [(258 : Vertex), (267 : Vertex), (282 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 1 = false ∨ valuation q 44 = false ∨ valuation q 47 = false := by
  rw [value1, value44, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (265 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 1 = false ∨ valuation q 44 = false ∨ valuation q 48 = false := by
  rw [value1, value44, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 1 = false ∨ valuation q 44 = false ∨ valuation q 59 = false := by
  rw [value1, value44, value49, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 1 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value1, value47, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (265 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 1 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value1, value47, value49, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (265 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 1 = false ∨ valuation q 48 = false ∨ valuation q 59 = false := by
  rw [value1, value48, value49, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 51 = true ∨ valuation q 84 = true := by
  rw [value50, value51, value84, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(270 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (260 : Vertex) [(270 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 45 = true ∨ valuation q 84 = true := by
  rw [value45, value50, value84, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 45 = true ∨ valuation q 51 = true := by
  rw [value45, value50, value51, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(260 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (396 : Vertex) [(260 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 50 = false ∨ valuation q 86 = false := by
  rw [value48, value50, value51, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (266 : Vertex) (268 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 88 = false := by
  rw [value52, value53, value56, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 169 = true ∨ valuation q 45 = true ∨ valuation q 52 = true := by
  rw [value45, value52, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 46 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value46, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 60 = true := by
  rw [value55, value60, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 171 = true ∨ valuation q 54 = true := by
  rw [value54, value55, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 4 = false ∨ valuation q 57 = false ∨ valuation q 93 = false := by
  rw [value4, value56, value57, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (24 : Vertex) (281 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 47 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value47, value56, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 47 = false ∨ valuation q 56 = false ∨ valuation q 94 = false := by
  rw [value47, value56, value57, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E120.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112120
