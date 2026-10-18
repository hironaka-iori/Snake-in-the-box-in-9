import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 48 = true := by
  rw [value48, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (209 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 11 = true ∨ valuation q 37 = true ∨ valuation q 47 = true ∨ valuation q 52 = true := by
  rw [value11, value37, value47, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ∈ [(81 : Vertex), (193 : Vertex), (208 : Vertex), (217 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (209 : Vertex) [(81 : Vertex), (193 : Vertex), (208 : Vertex), (217 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 11 = false ∨ valuation q 37 = false ∨ valuation q 52 = false := by
  rw [value11, value37, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (193 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 11 = false ∨ valuation q 47 = false ∨ valuation q 52 = false := by
  rw [value11, value47, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (81 : Vertex) (208 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 52 = false := by
  rw [value37, value47, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (193 : Vertex) (208 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 11 = false ∨ valuation q 37 = false := by
  rw [value11, value37, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (209 : Vertex) (81 : Vertex) (193 : Vertex) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 11 = false ∨ valuation q 47 = false := by
  rw [value11, value47, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (209 : Vertex) (81 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 37 = false ∨ valuation q 52 = false := by
  rw [value37, value52, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (209 : Vertex) (193 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 47 = false ∨ valuation q 52 = false := by
  rw [value47, value52, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (209 : Vertex) (208 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 175 = true ∨ valuation q 37 = true ∨ valuation q 47 = true ∨ valuation q 52 = true := by
  rw [value37, value47, value48, value52, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(193 : Vertex), (208 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (81 : Vertex) [(193 : Vertex), (208 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 175 = true ∨ valuation q 11 = true ∨ valuation q 47 = true ∨ valuation q 52 = true := by
  rw [value11, value47, value48, value52, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(81 : Vertex), (208 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (193 : Vertex) [(81 : Vertex), (208 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 175 = true ∨ valuation q 11 = true ∨ valuation q 37 = true ∨ valuation q 52 = true := by
  rw [value11, value37, value48, value52, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(81 : Vertex), (193 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (208 : Vertex) [(81 : Vertex), (193 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 175 = true ∨ valuation q 11 = true ∨ valuation q 37 = true ∨ valuation q 47 = true := by
  rw [value11, value37, value47, value48, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (209 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(81 : Vertex), (193 : Vertex), (208 : Vertex)] := by decide
  have hg := other_cover q (209 : Vertex) (217 : Vertex) [(81 : Vertex), (193 : Vertex), (208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 47 = false ∨ valuation q 53 = false := by
  rw [value38, value47, value49, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (208 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 53 = false ∨ valuation q 66 = false := by
  rw [value38, value49, value53, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (218 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 38 = false ∨ valuation q 53 = false ∨ valuation q 112 = false := by
  rw [value38, value49, value53, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (194 : Vertex) (218 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 66 = false ∨ valuation q 112 = false := by
  rw [value49, value53, value66, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (210 : Vertex) (218 : Vertex) (242 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 176 = true ∨ valuation q 38 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 66 = true := by
  rw [value38, value47, value49, value53, value66, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (210 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(194 : Vertex), (208 : Vertex), (218 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (210 : Vertex) (466 : Vertex) [(194 : Vertex), (208 : Vertex), (218 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 39 = false ∨ valuation q 47 = false := by
  rw [value13, value39, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 39 = false ∨ valuation q 54 = false := by
  rw [value13, value39, value50, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 39 = false ∨ valuation q 114 = false := by
  rw [value13, value39, value50, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (196 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 47 = false ∨ valuation q 54 = false := by
  rw [value13, value47, value50, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 13 = false ∨ valuation q 54 = false ∨ valuation q 114 = false := by
  rw [value13, value50, value54, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (84 : Vertex) (220 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 54 = false := by
  rw [value39, value47, value50, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (212 : Vertex) (196 : Vertex) (208 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 51 = true := by
  rw [value51, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (215 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = true ∨ valuation q 41 = true := by
  rw [value14, value41, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ∈ [(87 : Vertex), (199 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (215 : Vertex) [(87 : Vertex), (199 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 14 = false ∨ valuation q 41 = false := by
  rw [value14, value41, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (215 : Vertex) (87 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide)

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 41 = true := by
  rw [value41, value51, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(199 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (87 : Vertex) [(199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 178 = true ∨ valuation q 14 = true := by
  rw [value14, value51, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (199 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 179 = true ∨ valuation q 48 = true := by
  rw [value48, value52, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(209 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (89 : Vertex) [(209 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 179 = true ∨ valuation q 15 = true := by
  rw [value15, value52, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(89 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (209 : Vertex) [(89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value16, value42, value49, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (218 : Vertex) (90 : Vertex) (202 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E260.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112260
