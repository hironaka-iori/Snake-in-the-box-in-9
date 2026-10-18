import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value87, value90, value98, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (428 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 100 = false := by
  rw [value87, value88, value89, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value88, value89, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (427 : Vertex) (430 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 100 = true := by
  rw [value87, value88, value89, value91, value100, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(424 : Vertex), (427 : Vertex), (430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (418 : Vertex) [(424 : Vertex), (427 : Vertex), (430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 82 = true ∨ valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 100 = true := by
  rw [value82, value88, value89, value91, value100, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(418 : Vertex), (427 : Vertex), (430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (424 : Vertex) [(418 : Vertex), (427 : Vertex), (430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 100 = true := by
  rw [value82, value87, value88, value91, value100, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(418 : Vertex), (424 : Vertex), (430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (427 : Vertex) [(418 : Vertex), (424 : Vertex), (430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 100 = true := by
  rw [value82, value87, value88, value89, value100, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(418 : Vertex), (424 : Vertex), (427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(418 : Vertex), (424 : Vertex), (427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 210 = true ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 91 = true := by
  rw [value82, value87, value88, value89, value91, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(418 : Vertex), (424 : Vertex), (427 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (442 : Vertex) [(418 : Vertex), (424 : Vertex), (427 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 61 = false ∨ valuation q 88 = false := by
  rw [value26, value61, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 61 = false ∨ valuation q 92 = false := by
  rw [value26, value61, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 61 = false ∨ valuation q 101 = false := by
  rw [value26, value61, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 61 = false ∨ valuation q 110 = false := by
  rw [value26, value61, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 88 = false ∨ valuation q 92 = false := by
  rw [value26, value88, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value26, value88, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 92 = false ∨ valuation q 101 = false := by
  rw [value26, value89, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 92 = false ∨ valuation q 110 = false := by
  rw [value26, value89, value92, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (431 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 26 = false ∨ valuation q 101 = false ∨ valuation q 110 = false := by
  rw [value26, value89, value101, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 61 = false ∨ valuation q 88 = false ∨ valuation q 92 = false := by
  rw [value61, value88, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 61 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value61, value88, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 61 = false ∨ valuation q 88 = false ∨ valuation q 110 = false := by
  rw [value61, value88, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 61 = false ∨ valuation q 92 = false ∨ valuation q 101 = false := by
  rw [value61, value89, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 61 = false ∨ valuation q 92 = false ∨ valuation q 110 = false := by
  rw [value61, value89, value92, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (431 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 61 = false ∨ valuation q 101 = false ∨ valuation q 110 = false := by
  rw [value61, value89, value101, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 101 = false := by
  rw [value88, value89, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 110 = false := by
  rw [value88, value89, value92, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (431 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 110 = false := by
  rw [value88, value89, value101, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 101 = false ∨ valuation q 110 = false := by
  rw [value89, value92, value101, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (431 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 212 = true ∨ valuation q 87 = true ∨ valuation q 91 = true := by
  rw [value87, value90, value91, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(424 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(424 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 212 = true ∨ valuation q 83 = true ∨ valuation q 91 = true := by
  rw [value83, value90, value91, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(420 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (424 : Vertex) [(420 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 212 = true ∨ valuation q 83 = true ∨ valuation q 87 = true := by
  rw [value83, value87, value90, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value85, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 92 = false := by
  rw [value85, value88, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.First112
