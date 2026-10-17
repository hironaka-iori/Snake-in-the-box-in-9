import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 172 = true ∨ valuation q 45 = true ∨ valuation q 50 = true ∨ valuation q 100 = true := by
  rw [value45, value50, value52, value100, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(178 : Vertex), (184 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (190 : Vertex) [(178 : Vertex), (184 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 172 = true ∨ valuation q 45 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value45, value50, value52, value55, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(178 : Vertex), (184 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (442 : Vertex) [(178 : Vertex), (184 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 41 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value41, value47, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (172 : Vertex) (180 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 41 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value41, value50, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (172 : Vertex) (184 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 41 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value41, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (172 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 54 = false := by
  rw [value47, value50, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (180 : Vertex) (184 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 50 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value50, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (184 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 173 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 55 = true := by
  rw [value47, value50, value53, value54, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(180 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (172 : Vertex) [(180 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 173 = true ∨ valuation q 41 = true ∨ valuation q 50 = true ∨ valuation q 54 = true ∨ valuation q 55 = true := by
  rw [value41, value50, value53, value54, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(172 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (180 : Vertex) [(172 : Vertex), (184 : Vertex), (189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 173 = true ∨ valuation q 41 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value41, value47, value50, value53, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(172 : Vertex), (180 : Vertex), (184 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(172 : Vertex), (180 : Vertex), (184 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 53 = false := by
  rw [value42, value51, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (185 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 56 = false := by
  rw [value42, value51, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (185 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value42, value51, value54, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (185 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value42, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 102 = false := by
  rw [value42, value53, value54, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 42 = false ∨ valuation q 56 = false ∨ valuation q 102 = false := by
  rw [value42, value54, value56, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (191 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value51, value53, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (185 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 102 = false := by
  rw [value51, value53, value54, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (185 : Vertex) (188 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 102 = false := by
  rw [value51, value54, value56, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (185 : Vertex) (191 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 102 = false := by
  rw [value53, value54, value56, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (188 : Vertex) (191 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 51 = false ∨ valuation q 102 = false := by
  rw [value51, value102, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (189 : Vertex) (185 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide)

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 174 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 102 = true := by
  rw [value51, value53, value54, value56, value102, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(185 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(185 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 174 = true ∨ valuation q 42 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 102 = true := by
  rw [value42, value53, value54, value56, value102, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(173 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(173 : Vertex), (188 : Vertex), (191 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 174 = true ∨ valuation q 42 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 56 = true := by
  rw [value42, value51, value53, value54, value56, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(173 : Vertex), (185 : Vertex), (188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (445 : Vertex) [(173 : Vertex), (185 : Vertex), (188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 55 = true := by
  rw [value55, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (190 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = true ∨ valuation q 48 = true ∨ valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 56 = true ∨ valuation q 73 = true ∨ valuation q 103 = true := by
  rw [value15, value48, value52, value53, value55, value56, value73, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (190 : Vertex) w → w ∈ region → w ∈ [(62 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (254 : Vertex), (446 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (190 : Vertex) [(62 : Vertex), (182 : Vertex), (186 : Vertex), (188 : Vertex), (191 : Vertex), (254 : Vertex), (446 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value15, value48, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (182 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 53 = false := by
  rw [value15, value48, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (182 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value15, value48, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (182 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 73 = false := by
  rw [value15, value48, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (182 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 103 = false := by
  rw [value15, value48, value55, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (182 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 15 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value15, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (190 : Vertex) (62 : Vertex) (186 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E004.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112004
