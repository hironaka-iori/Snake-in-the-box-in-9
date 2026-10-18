import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value10, value76, value79, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 82 = false ∨ valuation q 111 = false := by
  rw [value10, value76, value82, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (379 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 56 = false ∨ valuation q 75 = false ∨ valuation q 82 = false := by
  rw [value56, value75, value76, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (307 : Vertex) (369 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 56 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value56, value76, value79, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (307 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 56 = false ∨ valuation q 82 = false ∨ valuation q 111 = false := by
  rw [value56, value76, value82, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (307 : Vertex) (379 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value75, value76, value79, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (369 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 79 = false ∨ valuation q 111 = false := by
  rw [value75, value76, value79, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (369 : Vertex) (375 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 75 = false ∨ valuation q 82 = false ∨ valuation q 111 = false := by
  rw [value75, value76, value82, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (369 : Vertex) (379 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 111 = false := by
  rw [value76, value79, value82, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (375 : Vertex) (379 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 193 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (356 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 193 = true ∨ valuation q 65 = true := by
  rw [value65, value77, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (372 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (372 : Vertex) (373 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 77 = false := by
  rw [value66, value75, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (369 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 66 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value66, value75, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (369 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 66 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value66, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 75 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value75, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (369 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 68 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value68, value78, value79, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (375 : Vertex) (359 : Vertex) (373 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 83 = true := by
  rw [value76, value78, value79, value83, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(371 : Vertex), (373 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (359 : Vertex) [(371 : Vertex), (373 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 68 = true ∨ valuation q 78 = true ∨ valuation q 83 = true := by
  rw [value68, value78, value79, value83, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(359 : Vertex), (373 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (371 : Vertex) [(359 : Vertex), (373 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 68 = true ∨ valuation q 76 = true ∨ valuation q 83 = true := by
  rw [value68, value76, value79, value83, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(359 : Vertex), (371 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(359 : Vertex), (371 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 195 = true ∨ valuation q 68 = true ∨ valuation q 76 = true ∨ valuation q 78 = true := by
  rw [value68, value76, value78, value79, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(359 : Vertex), (371 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (383 : Vertex) [(359 : Vertex), (371 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 196 = true ∨ valuation q 75 = true := by
  rw [value75, value80, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(369 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (379 : Vertex) [(369 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 58 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value58, value70, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (314 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 76 = true ∨ valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value76, value80, value81, value82, value83, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(371 : Vertex), (377 : Vertex), (378 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (363 : Vertex) [(371 : Vertex), (377 : Vertex), (378 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 71 = true ∨ valuation q 76 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value71, value76, value81, value82, value83, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(363 : Vertex), (371 : Vertex), (378 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (377 : Vertex) [(363 : Vertex), (371 : Vertex), (378 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 198 = true ∨ valuation q 71 = true ∨ valuation q 76 = true ∨ valuation q 80 = true ∨ valuation q 81 = true := by
  rw [value71, value76, value80, value81, value82, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(363 : Vertex), (371 : Vertex), (377 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (383 : Vertex) [(363 : Vertex), (371 : Vertex), (377 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 74 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value74, value79, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (367 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 203 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(390 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value93, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (403 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 99 = true := by
  rw [value96, value99, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (402 : Vertex) [(414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 212 = true ∨ valuation q 93 = true := by
  rw [value93, value96, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(402 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 101 = false := by
  rw [value27, value62, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (224 : Vertex) (352 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 104 = false := by
  rw [value27, value62, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (224 : Vertex) (352 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E058.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112058
