import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 25 = true ∨ valuation q 37 = true := by
  rw [value16, value18, value19, value20, value25, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex), (135 : Vertex), (142 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (6 : Vertex) [(130 : Vertex), (132 : Vertex), (135 : Vertex), (142 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 4 = true ∨ valuation q 16 = true ∨ valuation q 20 = true ∨ valuation q 25 = true ∨ valuation q 37 = true := by
  rw [value4, value16, value19, value20, value25, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(6 : Vertex), (130 : Vertex), (135 : Vertex), (142 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (132 : Vertex) [(6 : Vertex), (130 : Vertex), (135 : Vertex), (142 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 4 = true ∨ valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 25 = true ∨ valuation q 37 = true := by
  rw [value4, value16, value18, value19, value25, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(6 : Vertex), (130 : Vertex), (132 : Vertex), (142 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (135 : Vertex) [(6 : Vertex), (130 : Vertex), (132 : Vertex), (142 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 4 = true ∨ valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 37 = true := by
  rw [value4, value16, value18, value19, value20, value37, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(6 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (142 : Vertex) [(6 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 137 = true ∨ valuation q 4 = true ∨ valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 25 = true := by
  rw [value4, value16, value18, value19, value20, value25, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(6 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (198 : Vertex) [(6 : Vertex), (130 : Vertex), (132 : Vertex), (135 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 29 = false := by
  rw [value17, value19, value20, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 38 = false := by
  rw [value17, value19, value20, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 85 = false := by
  rw [value17, value19, value20, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 29 = false ∨ valuation q 38 = false := by
  rw [value17, value20, value29, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 29 = false ∨ valuation q 85 = false := by
  rw [value17, value20, value29, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 38 = false ∨ valuation q 85 = false := by
  rw [value17, value20, value38, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 29 = false ∨ valuation q 38 = false := by
  rw [value19, value20, value29, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 29 = false ∨ valuation q 85 = false := by
  rw [value19, value20, value29, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (151 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 19 = false ∨ valuation q 38 = false ∨ valuation q 85 = false := by
  rw [value19, value20, value38, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 29 = false ∨ valuation q 38 = false ∨ valuation q 85 = false := by
  rw [value20, value29, value38, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (151 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 138 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 29 = true ∨ valuation q 85 = true := by
  rw [value17, value19, value20, value29, value85, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (135 : Vertex) w → w ∈ region → w ≠ (199 : Vertex) → w ∈ [(131 : Vertex), (134 : Vertex), (151 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (135 : Vertex) (199 : Vertex) [(131 : Vertex), (134 : Vertex), (151 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value15, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (138 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value15, value21, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 15 = false ∨ valuation q 22 = false ∨ valuation q 39 = false := by
  rw [value15, value21, value22, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (137 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value15, value21, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 39 = false := by
  rw [value15, value21, value23, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (138 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value15, value21, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (128 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value21, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 39 = false := by
  rw [value21, value22, value23, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value21, value22, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 39 = false := by
  rw [value21, value23, value24, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 140 = true ∨ valuation q 21 = true ∨ valuation q 40 = true ∨ valuation q 86 = true := by
  rw [value21, value22, value40, value86, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(136 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (153 : Vertex) [(136 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 140 = true ∨ valuation q 21 = true ∨ valuation q 30 = true ∨ valuation q 40 = true := by
  rw [value21, value22, value30, value40, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(136 : Vertex), (153 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 16 = false ∨ valuation q 25 = false ∨ valuation q 31 = false := by
  rw [value16, value23, value25, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (130 : Vertex) (142 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 31 = false := by
  rw [value21, value23, value25, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (136 : Vertex) (142 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 25 = true ∨ valuation q 31 = true ∨ valuation q 87 = true := by
  rw [value16, value23, value25, value31, value87, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(130 : Vertex), (142 : Vertex), (154 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (136 : Vertex) [(130 : Vertex), (142 : Vertex), (154 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 141 = true ∨ valuation q 16 = true ∨ valuation q 21 = true ∨ valuation q 31 = true ∨ valuation q 87 = true := by
  rw [value16, value21, value23, value31, value87, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex), (154 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (142 : Vertex) [(130 : Vertex), (136 : Vertex), (154 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E027.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112027
