import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 140 = true ∨ valuation q 23 = true ∨ valuation q 25 = true ∨ valuation q 32 = true := by
  rw [value23, value25, value26, value32, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (134 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(130 : Vertex), (132 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (134 : Vertex) (135 : Vertex) [(130 : Vertex), (132 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 36 = false := by
  rw [value24, value26, value27, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 47 = false := by
  rw [value24, value26, value27, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 84 = false := by
  rw [value24, value26, value27, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (134 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 36 = false ∨ valuation q 47 = false := by
  rw [value24, value27, value36, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 36 = false ∨ valuation q 84 = false := by
  rw [value24, value27, value36, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (151 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 24 = false ∨ valuation q 47 = false ∨ valuation q 84 = false := by
  rw [value24, value27, value47, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 36 = false ∨ valuation q 47 = false := by
  rw [value26, value27, value36, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (151 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 36 = false ∨ valuation q 84 = false := by
  rw [value26, value27, value36, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (151 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = false ∨ valuation q 47 = false ∨ valuation q 84 = false := by
  rw [value26, value27, value47, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (134 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 36 = false ∨ valuation q 47 = false ∨ valuation q 84 = false := by
  rw [value27, value36, value47, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (151 : Vertex) (199 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value28, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 85 = false := by
  rw [value28, value29, value30, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (138 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 85 = false := by
  rw [value28, value29, value31, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (137 : Vertex) (140 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 85 = false := by
  rw [value28, value30, value31, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (392 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value29, value31, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (136 : Vertex) (137 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 143 = true ∨ valuation q 37 = true ∨ valuation q 48 = true ∨ valuation q 86 = true := by
  rw [value29, value37, value48, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(153 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (136 : Vertex) [(153 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 143 = true ∨ valuation q 28 = true ∨ valuation q 48 = true ∨ valuation q 86 = true := by
  rw [value28, value29, value48, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(136 : Vertex), (201 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (153 : Vertex) [(136 : Vertex), (201 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 143 = true ∨ valuation q 28 = true ∨ valuation q 37 = true ∨ valuation q 86 = true := by
  rw [value28, value29, value37, value86, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (201 : Vertex) [(136 : Vertex), (153 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 143 = true ∨ valuation q 28 = true ∨ valuation q 37 = true ∨ valuation q 48 = true := by
  rw [value28, value29, value37, value48, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(136 : Vertex), (153 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(136 : Vertex), (153 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 49 = false := by
  rw [value23, value30, value32, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (130 : Vertex) (142 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 49 = false := by
  rw [value30, value32, value38, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (142 : Vertex) (154 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 28 = true ∨ valuation q 38 = true ∨ valuation q 49 = true := by
  rw [value23, value28, value30, value38, value49, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex), (154 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (142 : Vertex) [(130 : Vertex), (136 : Vertex), (154 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 144 = true ∨ valuation q 23 = true ∨ valuation q 28 = true ∨ valuation q 32 = true ∨ valuation q 38 = true := by
  rw [value23, value28, value30, value32, value38, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(130 : Vertex), (136 : Vertex), (142 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (202 : Vertex) [(130 : Vertex), (136 : Vertex), (142 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 25 = false ∨ valuation q 32 = false ∨ valuation q 50 = false := by
  rw [value25, value31, value32, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (132 : Vertex) (142 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 28 = true ∨ valuation q 32 = true ∨ valuation q 50 = true := by
  rw [value28, value31, value32, value50, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(136 : Vertex), (142 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (132 : Vertex) [(136 : Vertex), (142 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 25 = true ∨ valuation q 32 = true ∨ valuation q 50 = true := by
  rw [value25, value31, value32, value50, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(132 : Vertex), (142 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (136 : Vertex) [(132 : Vertex), (142 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 25 = true ∨ valuation q 28 = true ∨ valuation q 50 = true := by
  rw [value25, value28, value31, value50, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (142 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (142 : Vertex) [(132 : Vertex), (136 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 145 = true ∨ valuation q 25 = true ∨ valuation q 28 = true ∨ valuation q 32 = true := by
  rw [value25, value28, value31, value32, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(132 : Vertex), (136 : Vertex), (142 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (204 : Vertex) [(132 : Vertex), (136 : Vertex), (142 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value26, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (138 : Vertex) (140 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 26 = false ∨ valuation q 31 = false ∨ valuation q 52 = false := by
  rw [value26, value31, value32, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (134 : Vertex) (140 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 52 = false := by
  rw [value30, value31, value32, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (142 : Vertex) (138 : Vertex) (140 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E168.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112168
