import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value79, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (414 : Vertex) (406 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 187 = true ∨ valuation q 79 = true ∨ valuation q 81 = true := by
  rw [value79, value81, value83, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(406 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (410 : Vertex) [(406 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 187 = true ∨ valuation q 79 = true ∨ valuation q 80 = true := by
  rw [value79, value80, value83, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (414 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(406 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (414 : Vertex) (412 : Vertex) [(406 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 188 = true := by
  rw [value84, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (418 : Vertex) (422 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 74 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value74, value85, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (390 : Vertex) (430 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 189 = true ∨ valuation q 84 = true ∨ valuation q 88 = true ∨ valuation q 91 = true := by
  rw [value84, value85, value88, value91, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(418 : Vertex), (430 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (390 : Vertex) [(418 : Vertex), (430 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 189 = true ∨ valuation q 74 = true ∨ valuation q 84 = true ∨ valuation q 91 = true := by
  rw [value74, value84, value85, value91, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(390 : Vertex), (418 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (430 : Vertex) [(390 : Vertex), (418 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 189 = true ∨ valuation q 74 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value74, value84, value85, value88, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (422 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(390 : Vertex), (418 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (422 : Vertex) (486 : Vertex) [(390 : Vertex), (418 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 50 = false ∨ valuation q 75 = false ∨ valuation q 87 = false := by
  rw [value50, value75, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (392 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 50 = false ∨ valuation q 75 = false ∨ valuation q 93 = false := by
  rw [value50, value75, value86, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (392 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 50 = false ∨ valuation q 87 = false ∨ valuation q 93 = false := by
  rw [value50, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 93 = false := by
  rw [value75, value86, value87, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (392 : Vertex) (428 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 191 = true ∨ valuation q 88 = true := by
  rw [value87, value88, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (424 : Vertex) [(430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 191 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 192 = true ∨ valuation q 87 = true := by
  rw [value87, value88, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(428 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (422 : Vertex) [(428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 192 = true ∨ valuation q 85 = true := by
  rw [value85, value88, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(422 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 193 = true ∨ valuation q 93 = true := by
  rw [value89, value93, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 193 = true ∨ valuation q 90 = true := by
  rw [value89, value90, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(481 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 194 = true ∨ valuation q 89 = true ∨ valuation q 97 = true := by
  rw [value89, value90, value97, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (489 : Vertex) [(480 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 194 = true ∨ valuation q 89 = true ∨ valuation q 94 = true := by
  rw [value89, value90, value94, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (497 : Vertex) [(480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 85 = false ∨ valuation q 92 = false ∨ valuation q 100 = false := by
  rw [value85, value91, value92, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (422 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 195 = true ∨ valuation q 92 = true ∨ valuation q 100 = true := by
  rw [value91, value92, value100, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(487 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (422 : Vertex) [(487 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 91 = true ∨ valuation q 96 = true := by
  rw [value91, value92, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ∈ [(486 : Vertex), (495 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (487 : Vertex) [(486 : Vertex), (495 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 196 = true ∨ valuation q 96 = true := by
  rw [value92, value96, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 196 = true ∨ valuation q 91 = true := by
  rw [value91, value92, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (495 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 197 = true ∨ valuation q 86 = true ∨ valuation q 94 = true := by
  rw [value86, value93, value94, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(424 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (480 : Vertex) [(424 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 197 = true ∨ valuation q 86 = true ∨ valuation q 89 = true := by
  rw [value86, value89, value93, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(424 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (489 : Vertex) [(424 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 90 = false ∨ valuation q 93 = false ∨ valuation q 95 = false := by
  rw [value90, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (481 : Vertex) (488 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 198 = true ∨ valuation q 93 = true ∨ valuation q 95 = true := by
  rw [value93, value94, value95, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(488 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (481 : Vertex) [(488 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 103 = false := by
  rw [value94, value95, value96, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (493 : Vertex) (489 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 200 = true ∨ valuation q 95 = true := by
  rw [value95, value96, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(493 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (487 : Vertex) [(493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 201 = true ∨ valuation q 99 = true := by
  rw [value97, value99, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (481 : Vertex) [(499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E175.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112175
