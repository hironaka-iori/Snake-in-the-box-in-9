import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 64 = false := by
  rw [value56, value57, value58, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 57 = false ∨ valuation q 72 = false := by
  rw [value56, value57, value58, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (194 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value56, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (199 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 72 = false := by
  rw [value56, value58, value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value56, value58, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (193 : Vertex) (203 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 64 = false := by
  rw [value57, value58, value61, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (194 : Vertex) (199 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 72 = false := by
  rw [value57, value58, value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (194 : Vertex) (199 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value57, value58, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (194 : Vertex) (203 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 72 = false := by
  rw [value58, value61, value64, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (195 : Vertex) (199 : Vertex) (203 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 182 = true ∨ valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 64 = true ∨ valuation q 72 = true := by
  rw [value56, value57, value58, value64, value72, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (195 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(193 : Vertex), (194 : Vertex), (203 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (195 : Vertex) (199 : Vertex) [(193 : Vertex), (194 : Vertex), (203 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 182 = true ∨ valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 61 = true ∨ valuation q 72 = true := by
  rw [value56, value57, value58, value61, value72, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (195 : Vertex) w → w ∈ region → w ≠ (203 : Vertex) → w ∈ [(193 : Vertex), (194 : Vertex), (199 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (195 : Vertex) (203 : Vertex) [(193 : Vertex), (194 : Vertex), (199 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 66 = false := by
  rw [value56, value59, value61, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 61 = true ∨ valuation q 66 = true := by
  rw [value59, value61, value66, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (197 : Vertex) w → w ∈ region → w ≠ (193 : Vertex) → w ∈ [(199 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (197 : Vertex) (193 : Vertex) [(199 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 56 = true ∨ valuation q 66 = true := by
  rw [value56, value59, value66, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (197 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(193 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (197 : Vertex) (199 : Vertex) [(193 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 183 = true ∨ valuation q 56 = true ∨ valuation q 61 = true := by
  rw [value56, value59, value61, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (197 : Vertex) w → w ∈ region → w ≠ (205 : Vertex) → w ∈ [(193 : Vertex), (199 : Vertex)] := by decide
  have hg := other_cover q (197 : Vertex) (205 : Vertex) [(193 : Vertex), (199 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 57 = false := by
  rw [value22, value39, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (194 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 61 = false := by
  rw [value22, value39, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 67 = false := by
  rw [value22, value39, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 73 = false := by
  rw [value22, value39, value60, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 111 = false := by
  rw [value22, value39, value60, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value22, value57, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value22, value57, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (194 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 57 = false ∨ valuation q 73 = false := by
  rw [value22, value57, value60, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (194 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 57 = false ∨ valuation q 111 = false := by
  rw [value22, value57, value60, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (194 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value22, value60, value61, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (199 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 61 = false ∨ valuation q 73 = false := by
  rw [value22, value60, value61, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 61 = false ∨ valuation q 111 = false := by
  rw [value22, value60, value61, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (199 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 67 = false ∨ valuation q 73 = false := by
  rw [value22, value60, value67, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 67 = false ∨ valuation q 111 = false := by
  rw [value22, value60, value67, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (206 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 22 = false ∨ valuation q 73 = false ∨ valuation q 111 = false := by
  rw [value22, value60, value73, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 57 = false ∨ valuation q 61 = false := by
  rw [value39, value57, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (194 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 39 = false ∨ valuation q 57 = false ∨ valuation q 67 = false := by
  rw [value39, value57, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (134 : Vertex) (194 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E089.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112089
