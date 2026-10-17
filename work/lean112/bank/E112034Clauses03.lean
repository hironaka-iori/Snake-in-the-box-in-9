import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 20 = false ∨ valuation q 27 = false ∨ valuation q 30 = false := by
  rw [value20, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 20 = false ∨ valuation q 27 = false ∨ valuation q 31 = false := by
  rw [value20, value27, value28, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (184 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 20 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value20, value28, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (185 : Vertex) (169 : Vertex) (187 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 27 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value27, value28, value30, value31, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(184 : Vertex), (187 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (169 : Vertex) [(184 : Vertex), (187 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 20 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value20, value28, value30, value31, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(169 : Vertex), (187 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (184 : Vertex) [(169 : Vertex), (187 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 20 = true ∨ valuation q 27 = true ∨ valuation q 31 = true := by
  rw [value20, value27, value28, value31, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(169 : Vertex), (184 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (187 : Vertex) [(169 : Vertex), (184 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 156 = true ∨ valuation q 20 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value20, value27, value28, value30, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(169 : Vertex), (184 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (189 : Vertex) [(169 : Vertex), (184 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 101 = false := by
  rw [value27, value29, value30, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (186 : Vertex) (184 : Vertex) (187 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 157 = true ∨ valuation q 30 = true ∨ valuation q 101 = true := by
  rw [value29, value30, value101, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(187 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (184 : Vertex) [(187 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 157 = true ∨ valuation q 27 = true ∨ valuation q 101 = true := by
  rw [value27, value29, value101, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(184 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (187 : Vertex) [(184 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 157 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value27, value29, value30, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(184 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (442 : Vertex) [(184 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 21 = true ∨ valuation q 28 = true ∨ valuation q 29 = true := by
  rw [value21, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ∈ [(171 : Vertex), (185 : Vertex), (186 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (187 : Vertex) [(171 : Vertex), (185 : Vertex), (186 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value21, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 21 = true ∨ valuation q 29 = true := by
  rw [value21, value29, value30, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(171 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (185 : Vertex) [(171 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 21 = true ∨ valuation q 28 = true := by
  rw [value21, value28, value30, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (187 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(171 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (187 : Vertex) (186 : Vertex) [(171 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 103 = false := by
  rw [value24, value28, value31, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (181 : Vertex) (185 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 28 = true ∨ valuation q 103 = true := by
  rw [value28, value31, value103, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(185 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (181 : Vertex) [(185 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 24 = true ∨ valuation q 103 = true := by
  rw [value24, value31, value103, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(181 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(181 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 32 = true := by
  rw [value32, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (226 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = true ∨ valuation q 37 = true ∨ valuation q 107 = true := by
  rw [value32, value33, value37, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ∈ [(227 : Vertex), (234 : Vertex), (482 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (226 : Vertex) [(227 : Vertex), (234 : Vertex), (482 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 107 = false := by
  rw [value32, value33, value37, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (227 : Vertex) (234 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value33, value37, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (226 : Vertex) (227 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 37 = true ∨ valuation q 107 = true := by
  rw [value32, value37, value107, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (227 : Vertex) → w ∈ [(234 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (227 : Vertex) [(234 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 107 = true := by
  rw [value32, value33, value107, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(227 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (234 : Vertex) [(227 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 37 = true := by
  rw [value32, value33, value37, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (226 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(227 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (226 : Vertex) (482 : Vertex) [(227 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 38 = false ∨ valuation q 43 = false := by
  rw [value32, value33, value38, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (226 : Vertex) (235 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 43 = false ∨ valuation q 108 = false := by
  rw [value32, value33, value43, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (226 : Vertex) (243 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 161 = true ∨ valuation q 38 = true ∨ valuation q 43 = true ∨ valuation q 108 = true := by
  rw [value33, value38, value43, value108, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(235 : Vertex), (243 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (226 : Vertex) [(235 : Vertex), (243 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 161 = true ∨ valuation q 32 = true ∨ valuation q 43 = true ∨ valuation q 108 = true := by
  rw [value32, value33, value43, value108, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(226 : Vertex), (243 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (235 : Vertex) [(226 : Vertex), (243 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 161 = true ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 108 = true := by
  rw [value32, value33, value38, value108, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (243 : Vertex) [(226 : Vertex), (235 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 161 = true ∨ valuation q 32 = true ∨ valuation q 38 = true ∨ valuation q 43 = true := by
  rw [value32, value33, value38, value43, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (227 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(226 : Vertex), (235 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (227 : Vertex) (483 : Vertex) [(226 : Vertex), (235 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 16 = false ∨ valuation q 35 = false ∨ valuation q 44 = false := by
  rw [value16, value34, value35, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (164 : Vertex) (229 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E034.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112034
