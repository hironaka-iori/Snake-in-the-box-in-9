import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value67, value68, value72, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (363 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value68, value70, value72, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (359 : Vertex) (363 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 184 = true ∨ valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 72 = true := by
  rw [value67, value68, value70, value72, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(353 : Vertex), (359 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (371 : Vertex) [(353 : Vertex), (359 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value67, value69, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (357 : Vertex) (353 : Vertex) (359 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value52, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 52 = false ∨ valuation q 68 = false ∨ valuation q 75 = false := by
  rw [value52, value68, value70, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (359 : Vertex) (295 : Vertex) (355 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 71 = true ∨ valuation q 75 = true := by
  rw [value71, value72, value75, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(361 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (355 : Vertex) [(361 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 68 = true ∨ valuation q 75 = true := by
  rw [value68, value72, value75, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(355 : Vertex), (367 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (361 : Vertex) [(355 : Vertex), (367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 189 = true ∨ valuation q 69 = true ∨ valuation q 75 = true ∨ valuation q 82 = true := by
  rw [value69, value73, value75, value82, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (365 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(357 : Vertex), (367 : Vertex), (381 : Vertex)] := by decide
  have hg := other_cover q (365 : Vertex) (361 : Vertex) [(357 : Vertex), (367 : Vertex), (381 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 25 = false ∨ valuation q 56 = false ∨ valuation q 75 = false := by
  rw [value25, value56, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (110 : Vertex) (302 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 25 = false ∨ valuation q 75 = false ∨ valuation q 83 = false := by
  rw [value25, value74, value75, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (110 : Vertex) (367 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 190 = true ∨ valuation q 25 = true ∨ valuation q 56 = true ∨ valuation q 83 = true := by
  rw [value25, value56, value74, value83, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(110 : Vertex), (302 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (367 : Vertex) [(110 : Vertex), (302 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 57 = false ∨ valuation q 70 = false := by
  rw [value26, value57, value70, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (303 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 57 = false ∨ valuation q 72 = false := by
  rw [value26, value57, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (303 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 57 = false ∨ valuation q 73 = false := by
  rw [value26, value57, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (303 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 57 = false ∨ valuation q 74 = false := by
  rw [value26, value57, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (303 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value26, value70, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (359 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value26, value70, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (359 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value26, value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (359 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value26, value72, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (363 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value26, value72, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (363 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 26 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value26, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (365 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 57 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value57, value70, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (303 : Vertex) (359 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 57 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value57, value70, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (303 : Vertex) (359 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 57 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value57, value70, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (303 : Vertex) (359 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 57 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value57, value72, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (303 : Vertex) (363 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 57 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value57, value72, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (303 : Vertex) (363 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 57 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value57, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (303 : Vertex) (365 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value70, value72, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (363 : Vertex) (365 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value70, value72, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (363 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 70 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value70, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (359 : Vertex) (365 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value72, value73, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (363 : Vertex) (365 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E051.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112051
