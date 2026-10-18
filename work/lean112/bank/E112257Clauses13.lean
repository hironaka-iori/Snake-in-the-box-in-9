import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 78 = true := by
  rw [value51, value61, value67, value72, value73, value74, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (188 : Vertex) → w ∈ [(152 : Vertex), (168 : Vertex), (176 : Vertex), (185 : Vertex), (186 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (188 : Vertex) [(152 : Vertex), (168 : Vertex), (176 : Vertex), (185 : Vertex), (186 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 51 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 76 = true := by
  rw [value51, value61, value67, value72, value73, value74, value76, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (184 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(152 : Vertex), (168 : Vertex), (176 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex)] := by decide
  have hg := other_cover q (184 : Vertex) (248 : Vertex) [(152 : Vertex), (168 : Vertex), (176 : Vertex), (185 : Vertex), (186 : Vertex), (188 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value32, value52, value62, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (153 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 52 = false ∨ valuation q 72 = false := by
  rw [value32, value52, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (153 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 52 = false ∨ valuation q 75 = false := by
  rw [value32, value52, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (153 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 52 = false ∨ valuation q 114 = false := by
  rw [value32, value52, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (153 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 72 = false := by
  rw [value32, value62, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (169 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 75 = false := by
  rw [value32, value62, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (169 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 114 = false := by
  rw [value32, value62, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (169 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value32, value72, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (184 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 72 = false ∨ valuation q 114 = false := by
  rw [value32, value72, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (184 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 32 = false ∨ valuation q 75 = false ∨ valuation q 114 = false := by
  rw [value32, value73, value75, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (57 : Vertex) (187 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 72 = false := by
  rw [value52, value62, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (153 : Vertex) (169 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 75 = false := by
  rw [value52, value62, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (153 : Vertex) (169 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 52 = false ∨ valuation q 62 = false ∨ valuation q 114 = false := by
  rw [value52, value62, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (153 : Vertex) (169 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 52 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value52, value72, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (153 : Vertex) (184 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 52 = false ∨ valuation q 72 = false ∨ valuation q 114 = false := by
  rw [value52, value72, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (153 : Vertex) (184 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 52 = false ∨ valuation q 75 = false ∨ valuation q 114 = false := by
  rw [value52, value73, value75, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (153 : Vertex) (187 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 62 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value62, value72, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 62 = false ∨ valuation q 72 = false ∨ valuation q 114 = false := by
  rw [value62, value72, value73, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 62 = false ∨ valuation q 75 = false ∨ valuation q 114 = false := by
  rw [value62, value73, value75, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (187 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 72 = false ∨ valuation q 75 = false ∨ valuation q 114 = false := by
  rw [value72, value73, value75, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (184 : Vertex) (187 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 189 = true ∨ valuation q 32 = true ∨ valuation q 62 = true ∨ valuation q 72 = true ∨ valuation q 75 = true ∨ valuation q 114 = true := by
  rw [value32, value62, value72, value73, value75, value114, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(57 : Vertex), (169 : Vertex), (184 : Vertex), (187 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (153 : Vertex) [(57 : Vertex), (169 : Vertex), (184 : Vertex), (187 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 189 = true ∨ valuation q 32 = true ∨ valuation q 52 = true ∨ valuation q 62 = true ∨ valuation q 72 = true ∨ valuation q 114 = true := by
  rw [value32, value52, value62, value72, value73, value114, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(57 : Vertex), (153 : Vertex), (169 : Vertex), (184 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (187 : Vertex) [(57 : Vertex), (153 : Vertex), (169 : Vertex), (184 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 189 = true ∨ valuation q 32 = true ∨ valuation q 52 = true ∨ valuation q 62 = true ∨ valuation q 72 = true ∨ valuation q 75 = true := by
  rw [value32, value52, value62, value72, value73, value75, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(57 : Vertex), (153 : Vertex), (169 : Vertex), (184 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (441 : Vertex) [(57 : Vertex), (153 : Vertex), (169 : Vertex), (184 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 63 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value63, value68, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (170 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 63 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value63, value72, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (170 : Vertex) (184 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 68 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value68, value72, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (178 : Vertex) (184 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 69 = false := by
  rw [value33, value53, value69, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (59 : Vertex) (155 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 53 = false ∨ valuation q 115 = false := by
  rw [value33, value53, value75, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (59 : Vertex) (155 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 69 = false ∨ valuation q 73 = false := by
  rw [value33, value69, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (59 : Vertex) (179 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 33 = false ∨ valuation q 69 = false ∨ valuation q 115 = false := by
  rw [value33, value69, value75, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (59 : Vertex) (179 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E257.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112257
