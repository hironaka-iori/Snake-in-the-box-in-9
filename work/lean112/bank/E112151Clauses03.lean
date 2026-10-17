import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 182 = true ∨ valuation q 77 = true ∨ valuation q 81 = true := by
  rw [value75, value77, value81, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(421 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (161 : Vertex) [(421 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 182 = true ∨ valuation q 11 = true ∨ valuation q 81 = true := by
  rw [value11, value75, value81, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(161 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (421 : Vertex) [(161 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 183 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value76, value77, value78, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(421 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (436 : Vertex) [(421 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value75, value76, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 13 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value13, value76, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 13 = false ∨ valuation q 79 = false ∨ valuation q 87 = false := by
  rw [value13, value78, value79, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (423 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 13 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value13, value78, value87, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (438 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 79 = false ∨ valuation q 87 = false := by
  rw [value76, value78, value79, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 79 = false ∨ valuation q 100 = false := by
  rw [value76, value78, value79, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value76, value78, value87, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (420 : Vertex) (438 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 87 = false ∨ valuation q 100 = false := by
  rw [value78, value79, value87, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (423 : Vertex) (438 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 186 = true ∨ valuation q 78 = true ∨ valuation q 84 = true := by
  rw [value78, value79, value84, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(422 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (421 : Vertex) [(422 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 186 = true ∨ valuation q 77 = true ∨ valuation q 84 = true := by
  rw [value77, value79, value84, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(421 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (422 : Vertex) [(421 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 186 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value79, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(421 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (431 : Vertex) [(421 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 187 = true ∨ valuation q 82 = true ∨ valuation q 88 = true := by
  rw [value80, value82, value88, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(426 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (425 : Vertex) [(426 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 187 = true ∨ valuation q 81 = true ∨ valuation q 88 = true := by
  rw [value80, value81, value88, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(425 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (426 : Vertex) [(425 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 187 = true ∨ valuation q 81 = true ∨ valuation q 82 = true := by
  rw [value80, value81, value82, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(425 : Vertex), (426 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (440 : Vertex) [(425 : Vertex), (426 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 83 = false := by
  rw [value75, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (424 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 89 = false := by
  rw [value75, value80, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (424 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 80 = false ∨ valuation q 101 = false := by
  rw [value75, value80, value81, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (424 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value75, value81, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (427 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 83 = false ∨ valuation q 101 = false := by
  rw [value75, value81, value83, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (427 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 75 = false ∨ valuation q 89 = false ∨ valuation q 101 = false := by
  rw [value75, value81, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (441 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value80, value81, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (424 : Vertex) (427 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 83 = false ∨ valuation q 101 = false := by
  rw [value80, value81, value83, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (424 : Vertex) (427 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 89 = false ∨ valuation q 101 = false := by
  rw [value80, value81, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (424 : Vertex) (441 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 89 = false ∨ valuation q 101 = false := by
  rw [value81, value83, value89, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (427 : Vertex) (441 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value80, value82, value83, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (424 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 189 = true ∨ valuation q 83 = true ∨ valuation q 90 = true := by
  rw [value82, value83, value90, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (424 : Vertex) [(427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 91 = false := by
  rw [value81, value82, value83, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (425 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 91 = false := by
  rw [value81, value83, value84, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (425 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 91 = false := by
  rw [value82, value83, value84, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E151.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112151
