import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 186 = true ∨ valuation q 64 = true ∨ valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 73 = true := by
  rw [value64, value69, value70, value71, value73, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(354 : Vertex), (360 : Vertex), (363 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (378 : Vertex) [(354 : Vertex), (360 : Vertex), (363 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 70 = false := by
  rw [value5, value51, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (299 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 82 = false := by
  rw [value5, value51, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (299 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 5 = false ∨ valuation q 51 = false ∨ valuation q 106 = false := by
  rw [value5, value51, value71, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (299 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 5 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value5, value70, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 5 = false ∨ valuation q 82 = false ∨ valuation q 106 = false := by
  rw [value5, value71, value82, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (379 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 51 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value51, value70, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (362 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 51 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value51, value70, value71, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 51 = false ∨ valuation q 70 = false ∨ valuation q 106 = false := by
  rw [value51, value70, value71, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (362 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 51 = false ∨ valuation q 74 = false ∨ valuation q 82 = false := by
  rw [value51, value71, value74, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (367 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 74 = false ∨ valuation q 82 = false := by
  rw [value70, value71, value74, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (362 : Vertex) (367 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 69 = true ∨ valuation q 73 = true := by
  rw [value69, value72, value73, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(360 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (356 : Vertex) [(360 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 65 = true ∨ valuation q 73 = true := by
  rw [value65, value72, value73, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(356 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (360 : Vertex) [(356 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 188 = true ∨ valuation q 65 = true ∨ valuation q 69 = true := by
  rw [value65, value69, value72, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(356 : Vertex), (360 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (366 : Vertex) [(356 : Vertex), (360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 72 = false := by
  rw [value67, value70, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (358 : Vertex) (362 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value67, value70, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (358 : Vertex) (362 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value67, value72, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (358 : Vertex) (364 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value70, value72, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (362 : Vertex) (364 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 53 = false ∨ valuation q 68 = false := by
  rw [value7, value53, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (303 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 53 = false ∨ valuation q 73 = false := by
  rw [value7, value53, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (303 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value7, value68, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (359 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 7 = false ∨ valuation q 68 = false ∨ valuation q 108 = false := by
  rw [value7, value68, value74, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (111 : Vertex) (359 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 53 = false ∨ valuation q 68 = false ∨ valuation q 71 = false := by
  rw [value53, value68, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (367 : Vertex) (303 : Vertex) (359 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 8 = false ∨ valuation q 54 = false ∨ valuation q 78 = false := by
  rw [value8, value54, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (369 : Vertex) (113 : Vertex) (305 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 8 = false ∨ valuation q 54 = false ∨ valuation q 109 = false := by
  rw [value8, value54, value75, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (369 : Vertex) (113 : Vertex) (305 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 56 = false ∨ valuation q 75 = false := by
  rw [value10, value56, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (307 : Vertex) (369 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 56 = false ∨ valuation q 79 = false := by
  rw [value10, value56, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (307 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 56 = false ∨ valuation q 82 = false := by
  rw [value10, value56, value76, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (307 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 56 = false ∨ valuation q 111 = false := by
  rw [value10, value56, value76, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (307 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 75 = false ∨ valuation q 79 = false := by
  rw [value10, value75, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (369 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 75 = false ∨ valuation q 82 = false := by
  rw [value10, value75, value76, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (369 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 10 = false ∨ valuation q 75 = false ∨ valuation q 111 = false := by
  rw [value10, value75, value76, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (369 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E058.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112058
