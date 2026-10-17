import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 181 = true ∨ valuation q 75 = true ∨ valuation q 79 = true := by
  rw [value75, value77, value79, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(393 : Vertex), (399 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (413 : Vertex) [(393 : Vertex), (399 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 30 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value30, value78, value79, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (399 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 30 = false ∨ valuation q 79 = false ∨ valuation q 94 = false := by
  rw [value30, value78, value79, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (399 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 30 = false ∨ valuation q 89 = false ∨ valuation q 94 = false := by
  rw [value30, value78, value89, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 182 = true ∨ valuation q 30 = true ∨ valuation q 79 = true ∨ valuation q 94 = true := by
  rw [value30, value78, value79, value94, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(142 : Vertex), (399 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (414 : Vertex) [(142 : Vertex), (399 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value76, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (399 : Vertex) (395 : Vertex) (397 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 183 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value79, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (399 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(397 : Vertex), (398 : Vertex)] := by decide
  have hg := other_cover q (399 : Vertex) (395 : Vertex) [(397 : Vertex), (398 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value72, value80, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (384 : Vertex) (404 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 184 = true ∨ valuation q 72 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value72, value80, value81, value83, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (400 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(384 : Vertex), (402 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (400 : Vertex) (408 : Vertex) [(384 : Vertex), (402 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 31 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value31, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (146 : Vertex) (400 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 31 = false ∨ valuation q 80 = false ∨ valuation q 86 = false := by
  rw [value31, value80, value81, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (146 : Vertex) (400 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 31 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value31, value81, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (146 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 31 = false ∨ valuation q 84 = false ∨ valuation q 95 = false := by
  rw [value31, value81, value84, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (146 : Vertex) (406 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 31 = false ∨ valuation q 86 = false ∨ valuation q 95 = false := by
  rw [value31, value81, value86, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (146 : Vertex) (410 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value80, value81, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 95 = false := by
  rw [value80, value81, value82, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value80, value81, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value81, value82, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (403 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 95 = false := by
  rw [value81, value84, value86, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (406 : Vertex) (410 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 186 = true ∨ valuation q 32 = true ∨ valuation q 81 = true := by
  rw [value32, value81, value82, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(147 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (387 : Vertex) [(147 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 33 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value33, value80, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (148 : Vertex) (400 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 33 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value33, value80, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (148 : Vertex) (400 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 33 = false ∨ valuation q 84 = false ∨ valuation q 87 = false := by
  rw [value33, value83, value84, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (148 : Vertex) (406 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 188 = true ∨ valuation q 83 = true ∨ valuation q 89 = true := by
  rw [value83, value84, value89, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(404 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(404 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 188 = true ∨ valuation q 81 = true ∨ valuation q 89 = true := by
  rw [value81, value84, value89, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(402 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (404 : Vertex) [(402 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 188 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value81, value83, value84, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(402 : Vertex), (404 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(402 : Vertex), (404 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 80 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value80, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (400 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 189 = true ∨ valuation q 80 = true ∨ valuation q 87 = true := by
  rw [value80, value85, value87, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (410 : Vertex) → w ∈ [(400 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (410 : Vertex) [(400 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 190 = true ∨ valuation q 85 = true ∨ valuation q 89 = true := by
  rw [value85, value86, value89, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(408 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (402 : Vertex) [(408 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 190 = true ∨ valuation q 81 = true ∨ valuation q 89 = true := by
  rw [value81, value86, value89, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(402 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (408 : Vertex) [(402 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 190 = true ∨ valuation q 81 = true ∨ valuation q 85 = true := by
  rw [value81, value85, value86, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(402 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (414 : Vertex) [(402 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value83, value85, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (404 : Vertex) (408 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E094.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112094
