import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 46 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value46, value80, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (289 : Vertex) (416 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 93 = false := by
  rw [value80, value81, value84, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 104 = false := by
  rw [value80, value81, value84, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (421 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value80, value81, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (416 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 104 = false := by
  rw [value81, value84, value93, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value80, value82, value85, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (418 : Vertex) (416 : Vertex) (422 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value80, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 90 = false := by
  rw [value80, value83, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 95 = false := by
  rw [value80, value83, value84, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value80, value83, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value80, value83, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value80, value83, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 90 = false := by
  rw [value83, value84, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 95 = false := by
  rw [value83, value84, value85, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value83, value84, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (421 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 95 = false := by
  rw [value83, value85, value90, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 96 = true ∨ valuation q 105 = true := by
  rw [value81, value83, value84, value86, value96, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ∈ [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (421 : Vertex) [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 96 = false := by
  rw [value81, value83, value84, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 203 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 96 = true ∨ valuation q 105 = true := by
  rw [value83, value84, value86, value96, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(420 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (417 : Vertex) [(420 : Vertex), (423 : Vertex), (437 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 203 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 96 = true ∨ valuation q 105 = true := by
  rw [value81, value83, value84, value96, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(417 : Vertex), (420 : Vertex), (437 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (423 : Vertex) [(417 : Vertex), (420 : Vertex), (437 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 203 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 105 = true := by
  rw [value81, value83, value84, value86, value105, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(417 : Vertex), (420 : Vertex), (423 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(417 : Vertex), (420 : Vertex), (423 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 203 = true ∨ valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 86 = true ∨ valuation q 96 = true := by
  rw [value81, value83, value84, value86, value96, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (485 : Vertex) [(417 : Vertex), (420 : Vertex), (423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 86 = false ∨ valuation q 106 = false := by
  rw [value83, value85, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 31 = false ∨ valuation q 48 = false ∨ valuation q 84 = false := by
  rw [value31, value48, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (295 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 31 = false ∨ valuation q 48 = false ∨ valuation q 92 = false := by
  rw [value31, value48, value86, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (295 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 31 = false ∨ valuation q 48 = false ∨ valuation q 97 = false := by
  rw [value31, value48, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (295 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 31 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value31, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 31 = false ∨ valuation q 85 = false ∨ valuation q 97 = false := by
  rw [value31, value85, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 48 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value48, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (295 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 92 = false := by
  rw [value84, value85, value86, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 97 = false := by
  rw [value84, value85, value86, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 84 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value84, value86, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (421 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E187.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112187
