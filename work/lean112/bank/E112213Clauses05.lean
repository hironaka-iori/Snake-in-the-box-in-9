import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 32 = true := by
  rw [value15, value27, value29, value31, value32, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(64 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (81 : Vertex) [(64 : Vertex), (82 : Vertex), (84 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 29 = true ∨ valuation q 32 = true := by
  rw [value15, value27, value28, value29, value32, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(64 : Vertex), (81 : Vertex), (82 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (84 : Vertex) [(64 : Vertex), (81 : Vertex), (82 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 29 = true ∨ valuation q 31 = true := by
  rw [value15, value27, value28, value29, value31, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(64 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (88 : Vertex) [(64 : Vertex), (81 : Vertex), (82 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value16, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (81 : Vertex) (65 : Vertex) (80 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 145 = true ∨ valuation q 16 = true ∨ valuation q 27 = true := by
  rw [value16, value27, value28, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(65 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (83 : Vertex) [(65 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 27 = false := by
  rw [value8, value17, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (66 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 33 = false := by
  rw [value8, value17, value29, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (66 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 66 = false := by
  rw [value8, value17, value29, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (66 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 83 = false := by
  rw [value8, value17, value29, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (66 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value8, value27, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (80 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 33 = false := by
  rw [value8, value27, value29, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (80 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 66 = false := by
  rw [value8, value27, value29, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (80 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 83 = false := by
  rw [value8, value27, value29, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (80 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value8, value29, value30, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (83 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 30 = false ∨ valuation q 66 = false := by
  rw [value8, value29, value30, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (83 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 30 = false ∨ valuation q 83 = false := by
  rw [value8, value29, value30, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (83 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 33 = false ∨ valuation q 66 = false := by
  rw [value8, value29, value33, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (90 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value8, value29, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (90 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 8 = false ∨ valuation q 66 = false ∨ valuation q 83 = false := by
  rw [value8, value29, value66, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (210 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value17, value27, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (80 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 33 = false := by
  rw [value17, value27, value29, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (80 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 66 = false := by
  rw [value17, value27, value29, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (80 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 83 = false := by
  rw [value17, value27, value29, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (80 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value17, value29, value30, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (83 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 30 = false ∨ valuation q 66 = false := by
  rw [value17, value29, value30, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (83 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 30 = false ∨ valuation q 83 = false := by
  rw [value17, value29, value30, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (83 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 33 = false ∨ valuation q 66 = false := by
  rw [value17, value29, value33, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (90 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 33 = false ∨ valuation q 83 = false := by
  rw [value17, value29, value33, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (90 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 17 = false ∨ valuation q 66 = false ∨ valuation q 83 = false := by
  rw [value17, value29, value66, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (66 : Vertex) (210 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value27, value29, value30, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (80 : Vertex) (83 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 66 = false := by
  rw [value27, value29, value30, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (80 : Vertex) (83 : Vertex) (210 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 83 = false := by
  rw [value27, value29, value30, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (80 : Vertex) (83 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E213.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112213
