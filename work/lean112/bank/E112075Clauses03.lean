import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 73 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value73, value74, value78, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (417 : Vertex) (427 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 84 = false := by
  rw [value74, value76, value78, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (419 : Vertex) (423 : Vertex) (427 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value73, value75, value76, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (421 : Vertex) (417 : Vertex) (423 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 180 = true ∨ valuation q 76 = true ∨ valuation q 79 = true := by
  rw [value75, value76, value79, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(423 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (417 : Vertex) [(423 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 180 = true ∨ valuation q 73 = true ∨ valuation q 76 = true := by
  rw [value73, value75, value76, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(417 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (429 : Vertex) [(417 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 93 = false := by
  rw [value74, value75, value76, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (421 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 81 = false ∨ valuation q 93 = false := by
  rw [value74, value76, value81, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (431 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 181 = true ∨ valuation q 74 = true ∨ valuation q 75 = true ∨ valuation q 81 = true := by
  rw [value74, value75, value76, value81, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(419 : Vertex), (421 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (487 : Vertex) [(419 : Vertex), (421 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 73 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value73, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (427 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 182 = true ∨ valuation q 78 = true ∨ valuation q 79 = true := by
  rw [value77, value78, value79, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(427 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (417 : Vertex) [(427 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 182 = true ∨ valuation q 73 = true ∨ valuation q 79 = true := by
  rw [value73, value77, value79, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(417 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (427 : Vertex) [(417 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 183 = true ∨ valuation q 77 = true ∨ valuation q 81 = true := by
  rw [value77, value78, value81, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(425 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (419 : Vertex) [(425 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 183 = true ∨ valuation q 74 = true ∨ valuation q 81 = true := by
  rw [value74, value78, value81, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(419 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (425 : Vertex) [(419 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 184 = true ∨ valuation q 77 = true ∨ valuation q 81 = true ∨ valuation q 88 = true := by
  rw [value77, value79, value81, value88, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(425 : Vertex), (431 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (421 : Vertex) [(425 : Vertex), (431 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 184 = true ∨ valuation q 75 = true ∨ valuation q 81 = true ∨ valuation q 88 = true := by
  rw [value75, value79, value81, value88, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(421 : Vertex), (431 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (425 : Vertex) [(421 : Vertex), (431 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 184 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 88 = true := by
  rw [value75, value77, value79, value88, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(421 : Vertex), (425 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (431 : Vertex) [(421 : Vertex), (425 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 184 = true ∨ valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 81 = true := by
  rw [value75, value77, value79, value81, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(421 : Vertex), (425 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (445 : Vertex) [(421 : Vertex), (425 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 38 = false ∨ valuation q 81 = false ∨ valuation q 89 = false := by
  rw [value38, value80, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (431 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 185 = true ∨ valuation q 81 = true ∨ valuation q 89 = true ∨ valuation q 96 = true := by
  rw [value80, value81, value89, value96, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(431 : Vertex), (446 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (174 : Vertex) [(431 : Vertex), (446 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 185 = true ∨ valuation q 38 = true ∨ valuation q 89 = true ∨ valuation q 96 = true := by
  rw [value38, value80, value89, value96, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(174 : Vertex), (446 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (431 : Vertex) [(174 : Vertex), (446 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 185 = true ∨ valuation q 38 = true ∨ valuation q 81 = true ∨ valuation q 96 = true := by
  rw [value38, value80, value81, value96, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(174 : Vertex), (431 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (446 : Vertex) [(174 : Vertex), (431 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value39, value76, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (423 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 76 = false ∨ valuation q 79 = false := by
  rw [value39, value76, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (423 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 76 = false ∨ valuation q 80 = false := by
  rw [value39, value76, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 76 = false ∨ valuation q 97 = false := by
  rw [value39, value76, value81, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (423 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value39, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (427 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value39, value78, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 78 = false ∨ valuation q 97 = false := by
  rw [value39, value78, value81, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (427 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value39, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (429 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 79 = false ∨ valuation q 97 = false := by
  rw [value39, value79, value81, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (429 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 39 = false ∨ valuation q 80 = false ∨ valuation q 97 = false := by
  rw [value39, value80, value81, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (175 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value76, value78, value79, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E075.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112075
