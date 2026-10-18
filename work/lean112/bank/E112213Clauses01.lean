import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 131 = true ∨ valuation q 12 = true ∨ valuation q 53 = true := by
  rw [value12, value14, value53, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(25 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (21 : Vertex) [(25 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value1, value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (65 : Vertex) (66 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 21 = false := by
  rw [value1, value15, value16, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (65 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 27 = false := by
  rw [value1, value15, value16, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (65 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 56 = false := by
  rw [value1, value15, value16, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (65 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 16 = false ∨ valuation q 74 = false := by
  rw [value1, value15, value16, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (65 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value1, value15, value17, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (66 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 17 = false ∨ valuation q 27 = false := by
  rw [value1, value15, value17, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (66 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 17 = false ∨ valuation q 56 = false := by
  rw [value1, value15, value17, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (66 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 17 = false ∨ valuation q 74 = false := by
  rw [value1, value15, value17, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (66 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value1, value15, value21, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (72 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 21 = false ∨ valuation q 56 = false := by
  rw [value1, value15, value21, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (72 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 21 = false ∨ valuation q 74 = false := by
  rw [value1, value15, value21, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (72 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 27 = false ∨ valuation q 56 = false := by
  rw [value1, value15, value27, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (80 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 27 = false ∨ valuation q 74 = false := by
  rw [value1, value15, value27, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (80 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 1 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value1, value15, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (0 : Vertex) (192 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value15, value16, value17, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (66 : Vertex) (72 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 27 = false := by
  rw [value15, value16, value17, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (66 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 56 = false := by
  rw [value15, value16, value17, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (66 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value17, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (66 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value15, value16, value21, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (72 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 56 = false := by
  rw [value15, value16, value21, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (72 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value21, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (72 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 56 = false := by
  rw [value15, value16, value27, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (80 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 27 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value27, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (80 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (65 : Vertex) (192 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value15, value17, value21, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (66 : Vertex) (72 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 56 = false := by
  rw [value15, value17, value21, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (66 : Vertex) (72 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 74 = false := by
  rw [value15, value17, value21, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (66 : Vertex) (72 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 56 = false := by
  rw [value15, value17, value27, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (66 : Vertex) (80 : Vertex) (192 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 27 = false ∨ valuation q 74 = false := by
  rw [value15, value17, value27, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (66 : Vertex) (80 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 56 = false ∨ valuation q 74 = false := by
  rw [value15, value17, value56, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (64 : Vertex) (66 : Vertex) (192 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E213.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112213
