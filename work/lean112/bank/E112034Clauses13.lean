import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 107 = false := by
  rw [value86, value88, value89, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (419 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value86, value88, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (426 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value86, value88, value93, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 86 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value86, value88, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (434 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value88, value89, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (419 : Vertex) (426 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value88, value89, value93, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (419 : Vertex) (426 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value88, value89, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (419 : Vertex) (434 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 107 = false := by
  rw [value88, value93, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (426 : Vertex) (434 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 216 = true ∨ valuation q 52 = true ∨ valuation q 86 = true ∨ valuation q 93 = true ∨ valuation q 98 = true ∨ valuation q 107 = true := by
  rw [value52, value86, value88, value93, value98, value107, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(290 : Vertex), (416 : Vertex), (426 : Vertex), (434 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (419 : Vertex) [(290 : Vertex), (416 : Vertex), (426 : Vertex), (434 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value87, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (418 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 87 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value87, value89, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (423 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 99 = false := by
  rw [value88, value89, value91, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (418 : Vertex) (423 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 99 = false ∨ valuation q 108 = false := by
  rw [value89, value91, value99, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (423 : Vertex) (435 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 217 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 99 = true ∨ valuation q 108 = true := by
  rw [value88, value89, value91, value99, value108, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(418 : Vertex), (423 : Vertex), (435 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (417 : Vertex) [(418 : Vertex), (423 : Vertex), (435 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 217 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 99 = true ∨ valuation q 108 = true := by
  rw [value87, value89, value91, value99, value108, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex), (435 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (418 : Vertex) [(417 : Vertex), (423 : Vertex), (435 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 217 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 99 = true ∨ valuation q 108 = true := by
  rw [value87, value88, value89, value99, value108, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(417 : Vertex), (418 : Vertex), (435 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (423 : Vertex) [(417 : Vertex), (418 : Vertex), (435 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 217 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 108 = true := by
  rw [value87, value88, value89, value91, value108, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(417 : Vertex), (418 : Vertex), (423 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (435 : Vertex) [(417 : Vertex), (418 : Vertex), (423 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 217 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 99 = true := by
  rw [value87, value88, value89, value91, value99, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(417 : Vertex), (418 : Vertex), (423 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (483 : Vertex) [(417 : Vertex), (418 : Vertex), (423 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 53 = false ∨ valuation q 100 = false := by
  rw [value16, value53, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (164 : Vertex) (292 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 53 = false ∨ valuation q 109 = false := by
  rw [value16, value53, value90, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (164 : Vertex) (292 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 86 = false ∨ valuation q 100 = false := by
  rw [value16, value86, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (164 : Vertex) (416 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 16 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value16, value90, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (164 : Vertex) (436 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 53 = false ∨ valuation q 86 = false ∨ valuation q 100 = false := by
  rw [value53, value86, value90, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (292 : Vertex) (416 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 53 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value53, value90, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (292 : Vertex) (436 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 86 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value86, value90, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (436 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 18 = false ∨ valuation q 89 = false ∨ valuation q 95 = false := by
  rw [value18, value89, value91, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (419 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 18 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value18, value89, value91, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (419 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 18 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value18, value91, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 89 = false ∨ valuation q 95 = false ∨ valuation q 112 = false := by
  rw [value89, value91, value95, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value20, value87, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (169 : Vertex) (417 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 87 = false ∨ valuation q 114 = false := by
  rw [value20, value87, value92, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (169 : Vertex) (417 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 20 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value20, value92, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (169 : Vertex) (429 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E034.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112034
