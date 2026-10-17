import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value91, value103, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (417 : Vertex) (425 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 34 = true ∨ valuation q 103 = true := by
  rw [value34, value86, value103, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(161 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (425 : Vertex) [(161 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 96 = true := by
  rw [value87, value96, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(436 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (422 : Vertex) [(436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 88 = true := by
  rw [value87, value88, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(422 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (436 : Vertex) [(422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value87, value88, value89, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 212 = true ∨ valuation q 89 = true ∨ valuation q 93 = true := by
  rw [value88, value89, value93, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(423 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (420 : Vertex) [(423 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 212 = true ∨ valuation q 87 = true ∨ valuation q 89 = true := by
  rw [value87, value88, value89, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (430 : Vertex) [(420 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 37 = false ∨ valuation q 88 = false ∨ valuation q 106 = false := by
  rw [value37, value88, value89, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (422 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 107 = false := by
  rw [value90, value91, value92, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (425 : Vertex) (426 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 91 = true ∨ valuation q 107 = true := by
  rw [value90, value91, value107, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(425 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (426 : Vertex) [(425 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 90 = true ∨ valuation q 108 = true := by
  rw [value90, value91, value108, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(424 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (417 : Vertex) [(424 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 86 = true ∨ valuation q 108 = true := by
  rw [value86, value91, value108, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(417 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (424 : Vertex) [(417 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value90, value92, value93, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 216 = true ∨ valuation q 93 = true ∨ valuation q 98 = true := by
  rw [value92, value93, value98, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (424 : Vertex) [(430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 216 = true ∨ valuation q 90 = true ∨ valuation q 98 = true := by
  rw [value90, value92, value98, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(424 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(424 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 216 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value90, value92, value93, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(424 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (442 : Vertex) [(424 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 217 = true ∨ valuation q 88 = true := by
  rw [value88, value93, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(422 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (426 : Vertex) [(422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 98 = true ∨ valuation q 115 = true := by
  rw [value94, value98, value115, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(442 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (435 : Vertex) [(442 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 95 = true ∨ valuation q 115 = true := by
  rw [value94, value95, value115, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(435 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (442 : Vertex) [(435 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 218 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value94, value95, value98, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(435 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (498 : Vertex) [(435 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 99 = false ∨ valuation q 116 = false := by
  rw [value94, value95, value99, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (434 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 99 = true ∨ valuation q 116 = true := by
  rw [value95, value99, value116, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(443 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (434 : Vertex) [(443 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 94 = true ∨ valuation q 116 = true := by
  rw [value94, value95, value116, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(434 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (443 : Vertex) [(434 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 44 = false ∨ valuation q 97 = false ∨ valuation q 117 = false := by
  rw [value44, value96, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (180 : Vertex) (437 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 87 = true ∨ valuation q 97 = true ∨ valuation q 117 = true := by
  rw [value87, value96, value97, value117, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (180 : Vertex) → w ∈ [(420 : Vertex), (437 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (180 : Vertex) [(420 : Vertex), (437 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 44 = true ∨ valuation q 87 = true ∨ valuation q 117 = true := by
  rw [value44, value87, value96, value117, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(180 : Vertex), (420 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(180 : Vertex), (420 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 220 = true ∨ valuation q 44 = true ∨ valuation q 87 = true ∨ valuation q 97 = true := by
  rw [value44, value87, value96, value97, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(180 : Vertex), (420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (500 : Vertex) [(180 : Vertex), (420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 100 = true := by
  rw [value97, value100, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(445 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 96 = true := by
  rw [value96, value97, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(436 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (445 : Vertex) [(436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 48 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value48, value92, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 48 = false ∨ valuation q 92 = false ∨ valuation q 99 = false := by
  rw [value48, value92, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 48 = false ∨ valuation q 94 = false ∨ valuation q 99 = false := by
  rw [value48, value94, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E020.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112020
