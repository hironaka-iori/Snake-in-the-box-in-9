import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 208 = true ∨ valuation q 90 = true ∨ valuation q 98 = true := by
  rw [value90, value92, value98, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(402 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (470 : Vertex) [(402 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 56 = false ∨ valuation q 88 = false ∨ valuation q 94 = false := by
  rw [value56, value88, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (400 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 56 = false ∨ valuation q 88 = false ∨ valuation q 96 = false := by
  rw [value56, value88, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (400 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 56 = false ∨ valuation q 88 = false ∨ valuation q 113 = false := by
  rw [value56, value88, value93, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (400 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 56 = false ∨ valuation q 94 = false ∨ valuation q 113 = false := by
  rw [value56, value93, value94, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (409 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 56 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value56, value93, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 56 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value56, value93, value95, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 56 = false ∨ valuation q 96 = false ∨ valuation q 113 = false := by
  rw [value56, value93, value96, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (412 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 88 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value88, value93, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (400 : Vertex) (409 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value88, value93, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (400 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 88 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value88, value93, value95, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (400 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value93, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value93, value94, value95, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 113 = false := by
  rw [value93, value95, value96, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (410 : Vertex) (412 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 211 = true ∨ valuation q 23 = true ∨ valuation q 58 = true ∨ valuation q 83 = true ∨ valuation q 93 = true ∨ valuation q 98 = true := by
  rw [value23, value58, value83, value93, value95, value98, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(154 : Vertex), (282 : Vertex), (394 : Vertex), (408 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (402 : Vertex) [(154 : Vertex), (282 : Vertex), (394 : Vertex), (408 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 211 = true ∨ valuation q 23 = true ∨ valuation q 58 = true ∨ valuation q 83 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value23, value58, value83, value90, value93, value95, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(154 : Vertex), (282 : Vertex), (394 : Vertex), (402 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(154 : Vertex), (282 : Vertex), (394 : Vertex), (402 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 93 = true ∨ valuation q 97 = true ∨ valuation q 98 = true := by
  rw [value93, value96, value97, value98, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(408 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (396 : Vertex) [(408 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 97 = true ∨ valuation q 98 = true := by
  rw [value84, value96, value97, value98, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(396 : Vertex), (413 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (408 : Vertex) [(396 : Vertex), (413 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 93 = true ∨ valuation q 98 = true := by
  rw [value84, value93, value96, value98, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(396 : Vertex), (408 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (413 : Vertex) [(396 : Vertex), (408 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 93 = true ∨ valuation q 97 = true := by
  rw [value84, value93, value96, value97, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(396 : Vertex), (408 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (414 : Vertex) [(396 : Vertex), (408 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value85, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (409 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 213 = true ∨ valuation q 25 = true ∨ valuation q 85 = true ∨ valuation q 94 = true := by
  rw [value25, value85, value94, value97, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(157 : Vertex), (397 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (412 : Vertex) [(157 : Vertex), (397 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value86, value92, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 92 = false ∨ valuation q 96 = false := by
  rw [value86, value92, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 86 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value86, value95, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value92, value95, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 78 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value78, value99, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (450 : Vertex) (386 : Vertex) (451 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 78 = true ∨ valuation q 104 = true := by
  rw [value78, value99, value104, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(386 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(386 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 215 = true ∨ valuation q 78 = true ∨ valuation q 100 = true := by
  rw [value78, value99, value100, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(386 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(386 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 216 = true ∨ valuation q 99 = true ∨ valuation q 105 = true := by
  rw [value99, value100, value105, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (387 : Vertex) [(450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 216 = true ∨ valuation q 79 = true ∨ valuation q 105 = true := by
  rw [value79, value100, value105, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(387 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(387 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 216 = true ∨ valuation q 79 = true ∨ valuation q 99 = true := by
  rw [value79, value99, value100, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(387 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(387 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E120.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112120
