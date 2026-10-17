import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value83, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (404 : Vertex) (413 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 191 = true ∨ valuation q 37 = true ∨ valuation q 83 = true ∨ valuation q 88 = true ∨ valuation q 89 = true ∨ valuation q 98 = true := by
  rw [value37, value83, value87, value88, value89, value98, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(156 : Vertex), (404 : Vertex), (413 : Vertex), (414 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (408 : Vertex) [(156 : Vertex), (404 : Vertex), (413 : Vertex), (414 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 77 = false ∨ valuation q 87 = false := by
  rw [value38, value77, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (157 : Vertex) (397 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 77 = false ∨ valuation q 99 = false := by
  rw [value38, value77, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (157 : Vertex) (397 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 38 = false ∨ valuation q 87 = false ∨ valuation q 99 = false := by
  rw [value38, value87, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (157 : Vertex) (412 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 77 = false ∨ valuation q 87 = false ∨ valuation q 99 = false := by
  rw [value77, value87, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (397 : Vertex) (412 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 78 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value78, value84, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 78 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value78, value84, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (406 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 78 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value78, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (398 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value84, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 194 = true ∨ valuation q 95 = true := by
  rw [value90, value95, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(466 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 194 = true ∨ valuation q 93 = true := by
  rw [value90, value93, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (466 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 195 = true ∨ valuation q 93 = true := by
  rw [value91, value93, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (457 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 195 = true ∨ valuation q 92 = true := by
  rw [value91, value92, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(457 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (458 : Vertex) [(457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 75 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value75, value91, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (393 : Vertex) (456 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 196 = true ∨ valuation q 75 = true ∨ valuation q 96 = true := by
  rw [value75, value92, value96, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(393 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (456 : Vertex) [(393 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 196 = true ∨ valuation q 75 = true ∨ valuation q 91 = true := by
  rw [value75, value91, value92, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(393 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (473 : Vertex) [(393 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value90, value91, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (450 : Vertex) (456 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 197 = true ∨ valuation q 91 = true ∨ valuation q 94 = true := by
  rw [value91, value93, value94, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(456 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (450 : Vertex) [(456 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 197 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value90, value93, value94, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(450 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (456 : Vertex) [(450 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 198 = true ∨ valuation q 78 = true := by
  rw [value78, value94, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(398 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (458 : Vertex) [(398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 199 = true ∨ valuation q 81 = true ∨ valuation q 100 = true := by
  rw [value81, value95, value100, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(402 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (450 : Vertex) [(402 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 199 = true ∨ valuation q 81 = true ∨ valuation q 90 = true := by
  rw [value81, value90, value95, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(402 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (498 : Vertex) [(402 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 200 = true ∨ valuation q 97 = true ∨ valuation q 99 = true := by
  rw [value96, value97, value99, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(475 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (457 : Vertex) [(475 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 200 = true ∨ valuation q 92 = true ∨ valuation q 97 = true := by
  rw [value92, value96, value97, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (477 : Vertex) → w ∈ [(457 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (477 : Vertex) [(457 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 201 = true := by
  rw [value97, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (475 : Vertex) (473 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 99 = false ∨ valuation q 104 = false := by
  rw [value87, value98, value99, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (477 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 202 = true ∨ valuation q 87 = true ∨ valuation q 99 = true := by
  rw [value87, value98, value99, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(412 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (508 : Vertex) [(412 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 203 = true ∨ valuation q 88 = true ∨ valuation q 98 = true := by
  rw [value88, value98, value99, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(413 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (473 : Vertex) [(413 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 203 = true ∨ valuation q 88 = true ∨ valuation q 96 = true := by
  rw [value88, value96, value99, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (477 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(413 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (477 : Vertex) (476 : Vertex) [(413 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 47 = false ∨ valuation q 65 = false ∨ valuation q 95 = false := by
  rw [value47, value65, value95, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (370 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 47 = false ∨ valuation q 65 = false ∨ valuation q 103 = false := by
  rw [value47, value65, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (370 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E094.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112094
