import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 44 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value44, value50, value71, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value50, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (185 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 71 = false := by
  rw [value50, value51, value52, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (185 : Vertex) (186 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 98 = false := by
  rw [value50, value51, value52, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (185 : Vertex) (186 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 71 = false := by
  rw [value50, value51, value53, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (185 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 98 = false := by
  rw [value50, value51, value53, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (185 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value50, value51, value71, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (185 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 71 = false := by
  rw [value50, value52, value53, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (186 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 98 = false := by
  rw [value50, value52, value53, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (186 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value50, value52, value71, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (186 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 71 = false ∨ valuation q 98 = false := by
  rw [value50, value53, value71, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (188 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 13 = false ∨ valuation q 98 = false := by
  rw [value13, value98, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (184 : Vertex) (56 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide)

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 54 = false := by
  rw [value14, value39, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (169 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 39 = false ∨ valuation q 72 = false := by
  rw [value14, value39, value51, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (169 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 99 = false := by
  rw [value14, value50, value51, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (184 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value14, value51, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (189 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 14 = false ∨ valuation q 72 = false ∨ valuation q 99 = false := by
  rw [value14, value51, value72, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (249 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 39 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value39, value50, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 39 = false ∨ valuation q 50 = false ∨ valuation q 72 = false := by
  rw [value39, value50, value51, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 39 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value39, value51, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (189 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 39 = false ∨ valuation q 54 = false ∨ valuation q 99 = false := by
  rw [value39, value51, value54, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (189 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 39 = false ∨ valuation q 72 = false ∨ valuation q 99 = false := by
  rw [value39, value51, value72, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (249 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 54 = false ∨ valuation q 72 = false := by
  rw [value50, value51, value54, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (184 : Vertex) (189 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 171 = true ∨ valuation q 39 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 72 = true ∨ valuation q 99 = true := by
  rw [value39, value50, value51, value54, value72, value99, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(169 : Vertex), (184 : Vertex), (189 : Vertex), (249 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (57 : Vertex) [(169 : Vertex), (184 : Vertex), (189 : Vertex), (249 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 171 = true ∨ valuation q 14 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 72 = true ∨ valuation q 99 = true := by
  rw [value14, value50, value51, value54, value72, value99, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(57 : Vertex), (184 : Vertex), (189 : Vertex), (249 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (169 : Vertex) [(57 : Vertex), (184 : Vertex), (189 : Vertex), (249 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 171 = true ∨ valuation q 14 = true ∨ valuation q 39 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 99 = true := by
  rw [value14, value39, value50, value51, value54, value99, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(57 : Vertex), (169 : Vertex), (184 : Vertex), (189 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (249 : Vertex) [(57 : Vertex), (169 : Vertex), (184 : Vertex), (189 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 171 = true ∨ valuation q 14 = true ∨ valuation q 39 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 72 = true := by
  rw [value14, value39, value50, value51, value54, value72, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(57 : Vertex), (169 : Vertex), (184 : Vertex), (189 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (441 : Vertex) [(57 : Vertex), (169 : Vertex), (184 : Vertex), (189 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value45, value50, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (178 : Vertex) (184 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 100 = false := by
  rw [value45, value50, value52, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (178 : Vertex) (184 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 100 = false := by
  rw [value50, value52, value55, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (184 : Vertex) (190 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 172 = true ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 100 = true := by
  rw [value50, value52, value55, value100, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(184 : Vertex), (190 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (178 : Vertex) [(184 : Vertex), (190 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 172 = true ∨ valuation q 45 = true ∨ valuation q 55 = true ∨ valuation q 100 = true := by
  rw [value45, value52, value55, value100, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(178 : Vertex), (190 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (184 : Vertex) [(178 : Vertex), (190 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block11 (q : Snake 81) (h : Conditions q) : B112E004.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112004
