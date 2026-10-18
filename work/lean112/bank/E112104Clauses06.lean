import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 15 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value15, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (353 : Vertex) (356 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 15 = false ∨ valuation q 62 = false ∨ valuation q 70 = false := by
  rw [value15, value62, value65, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (353 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 15 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value15, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (101 : Vertex) (359 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value64, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (356 : Vertex) (359 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 183 = true ∨ valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 70 = true := by
  rw [value62, value64, value65, value66, value70, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (101 : Vertex) → w ∈ [(353 : Vertex), (356 : Vertex), (359 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (101 : Vertex) [(353 : Vertex), (356 : Vertex), (359 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 101 = false := by
  rw [value63, value65, value66, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (355 : Vertex) (357 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 75 = false ∨ valuation q 104 = false := by
  rw [value67, value68, value75, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (363 : Vertex) (378 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 68 = true ∨ valuation q 75 = true ∨ valuation q 104 = true := by
  rw [value67, value68, value75, value104, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (106 : Vertex) → w ∈ [(363 : Vertex), (378 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (106 : Vertex) [(363 : Vertex), (378 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 18 = true ∨ valuation q 68 = true ∨ valuation q 75 = true := by
  rw [value18, value67, value68, value75, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(106 : Vertex), (363 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (490 : Vertex) [(106 : Vertex), (363 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 19 = false ∨ valuation q 63 = false ∨ valuation q 67 = false := by
  rw [value19, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (355 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 19 = false ∨ valuation q 63 = false ∨ valuation q 105 = false := by
  rw [value19, value63, value68, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (355 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 19 = false ∨ valuation q 67 = false ∨ valuation q 105 = false := by
  rw [value19, value67, value68, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (362 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 105 = false := by
  rw [value63, value67, value68, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 187 = true ∨ valuation q 64 = true ∨ valuation q 70 = true ∨ valuation q 106 = true := by
  rw [value64, value69, value70, value106, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(356 : Vertex), (365 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (108 : Vertex) [(356 : Vertex), (365 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 187 = true ∨ valuation q 20 = true ∨ valuation q 70 = true ∨ valuation q 106 = true := by
  rw [value20, value69, value70, value106, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(108 : Vertex), (365 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (356 : Vertex) [(108 : Vertex), (365 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 187 = true ∨ valuation q 20 = true ∨ valuation q 64 = true ∨ valuation q 106 = true := by
  rw [value20, value64, value69, value106, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(108 : Vertex), (356 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (365 : Vertex) [(108 : Vertex), (356 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value65, value69, value70, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (364 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 107 = false := by
  rw [value65, value69, value70, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (364 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 76 = false ∨ valuation q 107 = false := by
  rw [value65, value70, value76, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (381 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 76 = false ∨ valuation q 107 = false := by
  rw [value69, value70, value76, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (364 : Vertex) (381 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 189 = true ∨ valuation q 73 = true := by
  rw [value71, value73, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (369 : Vertex) → w ∈ [(370 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (369 : Vertex) [(370 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 190 = true ∨ valuation q 62 = true ∨ valuation q 71 = true := by
  rw [value62, value71, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (369 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(353 : Vertex), (368 : Vertex)] := by decide
  have hg := other_cover q (369 : Vertex) (113 : Vertex) [(353 : Vertex), (368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 190 = true ∨ valuation q 22 = true ∨ valuation q 71 = true := by
  rw [value22, value71, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (369 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(113 : Vertex), (368 : Vertex)] := by decide
  have hg := other_cover q (369 : Vertex) (353 : Vertex) [(113 : Vertex), (368 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 190 = true ∨ valuation q 22 = true ∨ valuation q 62 = true := by
  rw [value22, value62, value72, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (369 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(113 : Vertex), (353 : Vertex)] := by decide
  have hg := other_cover q (369 : Vertex) (368 : Vertex) [(113 : Vertex), (353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value71, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (370 : Vertex) (368 : Vertex) (374 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 191 = true ∨ valuation q 74 = true ∨ valuation q 75 = true := by
  rw [value73, value74, value75, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (368 : Vertex) → w ∈ [(374 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (368 : Vertex) [(374 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 77 = false ∨ valuation q 112 = false := by
  rw [value73, value74, value77, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (374 : Vertex) (370 : Vertex) (382 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 67 = false ∨ valuation q 73 = false ∨ valuation q 77 = false := by
  rw [value67, value73, value75, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (362 : Vertex) (370 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 117 = false := by
  rw [value70, value76, value78, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (365 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 78 = true ∨ valuation q 117 = true := by
  rw [value76, value78, value117, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(383 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (365 : Vertex) [(383 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 70 = true ∨ valuation q 117 = true := by
  rw [value70, value76, value117, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(365 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (383 : Vertex) [(365 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 194 = true ∨ valuation q 70 = true ∨ valuation q 78 = true := by
  rw [value70, value76, value78, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(365 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (509 : Vertex) [(365 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E104.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112104
