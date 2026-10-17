import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 156 = true ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 57 = true := by
  rw [value47, value48, value49, value57, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(269 : Vertex), (270 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (332 : Vertex) [(269 : Vertex), (270 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value3, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (261 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 45 = false ∨ valuation q 50 = false := by
  rw [value3, value45, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (261 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 45 = false ∨ valuation q 58 = false := by
  rw [value3, value45, value48, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (261 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 45 = false ∨ valuation q 68 = false := by
  rw [value3, value45, value48, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (261 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 47 = false ∨ valuation q 68 = false := by
  rw [value3, value47, value48, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (268 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 50 = false ∨ valuation q 58 = false := by
  rw [value3, value48, value50, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (271 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 50 = false ∨ valuation q 68 = false := by
  rw [value3, value48, value50, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 3 = false ∨ valuation q 58 = false ∨ valuation q 68 = false := by
  rw [value3, value48, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (13 : Vertex) (285 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value45, value47, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 58 = false := by
  rw [value45, value47, value48, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 68 = false := by
  rw [value45, value47, value48, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (268 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 58 = false := by
  rw [value45, value48, value50, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (271 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 68 = false := by
  rw [value45, value48, value50, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 45 = false ∨ valuation q 58 = false ∨ valuation q 68 = false := by
  rw [value45, value48, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (261 : Vertex) (285 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 58 = false := by
  rw [value47, value48, value50, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 68 = false := by
  rw [value47, value48, value50, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (268 : Vertex) (271 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 50 = false ∨ valuation q 58 = false ∨ valuation q 68 = false := by
  rw [value48, value50, value58, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (269 : Vertex) (271 : Vertex) (285 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 59 = false := by
  rw [value47, value49, value50, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (268 : Vertex) (271 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 158 = true ∨ valuation q 47 = true ∨ valuation q 59 = true := by
  rw [value47, value49, value59, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (271 : Vertex) → w ∈ [(268 : Vertex), (286 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (271 : Vertex) [(268 : Vertex), (286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 60 = false := by
  rw [value46, value49, value50, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (271 : Vertex) (267 : Vertex) (270 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 159 = true ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value48, value49, value50, value60, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(269 : Vertex), (270 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (267 : Vertex) [(269 : Vertex), (270 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 159 = true ∨ valuation q 46 = true ∨ valuation q 49 = true ∨ valuation q 60 = true := by
  rw [value46, value49, value50, value60, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(267 : Vertex), (270 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (269 : Vertex) [(267 : Vertex), (270 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 159 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 60 = true := by
  rw [value46, value48, value50, value60, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(267 : Vertex), (269 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (270 : Vertex) [(267 : Vertex), (269 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 159 = true ∨ valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 49 = true := by
  rw [value46, value48, value49, value50, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (271 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(267 : Vertex), (269 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (271 : Vertex) (287 : Vertex) [(267 : Vertex), (269 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value51, value52, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (273 : Vertex) (274 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 160 = true ∨ valuation q 52 = true ∨ valuation q 56 = true := by
  rw [value51, value52, value56, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(273 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (274 : Vertex) [(273 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 43 = false ∨ valuation q 51 = false := by
  rw [value4, value43, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 43 = false ∨ valuation q 54 = false := by
  rw [value4, value43, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 43 = false ∨ valuation q 69 = false := by
  rw [value4, value43, value52, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (257 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value4, value51, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (272 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 69 = false := by
  rw [value4, value51, value52, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (17 : Vertex) (272 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E166.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112166
