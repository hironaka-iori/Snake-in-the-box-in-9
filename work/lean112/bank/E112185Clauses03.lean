import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 135 = true ∨ valuation q 22 = true ∨ valuation q 28 = true := by
  rw [value22, value27, value28, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (84 : Vertex) [(69 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 27 = false ∨ valuation q 31 = false := by
  rw [value27, value31, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (87 : Vertex) (85 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 136 = true ∨ valuation q 31 = true := by
  rw [value28, value31, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 136 = true ∨ valuation q 27 = true := by
  rw [value27, value28, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (95 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 137 = true := by
  rw [value29, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (89 : Vertex) (91 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 138 = true ∨ valuation q 29 = true ∨ valuation q 31 = true := by
  rw [value29, value30, value31, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(89 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (75 : Vertex) [(89 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 138 = true ∨ valuation q 24 = true ∨ valuation q 29 = true := by
  rw [value24, value29, value30, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (91 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(75 : Vertex), (89 : Vertex)] := by decide
  have hg := other_cover q (91 : Vertex) (95 : Vertex) [(75 : Vertex), (89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 139 = true ∨ valuation q 19 = true ∨ valuation q 30 = true := by
  rw [value19, value30, value31, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(31 : Vertex), (91 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (87 : Vertex) [(31 : Vertex), (91 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 139 = true ∨ valuation q 19 = true ∨ valuation q 28 = true := by
  rw [value19, value28, value31, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(31 : Vertex), (87 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (91 : Vertex) [(31 : Vertex), (87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 140 = true ∨ valuation q 38 = true := by
  rw [value32, value38, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(176 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (161 : Vertex) [(176 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 140 = true ∨ valuation q 33 = true := by
  rw [value32, value33, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (176 : Vertex) → w ∈ [(161 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (176 : Vertex) [(161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 39 = true := by
  rw [value32, value33, value34, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ∈ [(160 : Vertex), (165 : Vertex), (177 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (161 : Vertex) [(160 : Vertex), (165 : Vertex), (177 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 39 = false := by
  rw [value32, value33, value34, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (161 : Vertex) (160 : Vertex) (165 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 141 = true ∨ valuation q 34 = true ∨ valuation q 39 = true := by
  rw [value33, value34, value39, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(165 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(165 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 141 = true ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value32, value33, value34, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (165 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (177 : Vertex) [(160 : Vertex), (165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 84 = false := by
  rw [value33, value34, value36, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 142 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value33, value34, value36, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (165 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(161 : Vertex), (173 : Vertex)] := by decide
  have hg := other_cover q (165 : Vertex) (421 : Vertex) [(161 : Vertex), (173 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 143 = true ∨ valuation q 85 = true := by
  rw [value35, value85, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (175 : Vertex) [(427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 143 = true ∨ valuation q 37 = true := by
  rw [value35, value37, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(175 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (427 : Vertex) [(175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 45 = false := by
  rw [value34, value36, value37, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 144 = true ∨ valuation q 34 = true ∨ valuation q 45 = true := by
  rw [value34, value36, value45, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(165 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(165 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 145 = true ∨ valuation q 36 = true ∨ valuation q 47 = true := by
  rw [value36, value37, value47, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(173 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (171 : Vertex) [(173 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 145 = true ∨ valuation q 35 = true ∨ valuation q 47 = true := by
  rw [value35, value37, value47, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(171 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [(171 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value32, value38, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 39 = false ∨ valuation q 43 = false := by
  rw [value32, value38, value39, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value32, value38, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 40 = false ∨ valuation q 86 = false := by
  rw [value32, value38, value40, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (178 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 32 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value32, value38, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (184 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value38, value39, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 86 = false := by
  rw [value38, value39, value40, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value38, value39, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (177 : Vertex) (184 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 43 = false ∨ valuation q 86 = false := by
  rw [value38, value40, value43, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (178 : Vertex) (184 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E185.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112185
