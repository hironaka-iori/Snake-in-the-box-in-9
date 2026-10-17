import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 57 = false := by
  rw [value34, value35, value37, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (164 : Vertex) (168 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 76 = false := by
  rw [value34, value35, value37, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (164 : Vertex) (168 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 57 = false ∨ valuation q 76 = false := by
  rw [value34, value35, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (164 : Vertex) (224 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 57 = false ∨ valuation q 76 = false := by
  rw [value34, value37, value57, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (168 : Vertex) (224 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 140 = true ∨ valuation q 37 = true ∨ valuation q 57 = true ∨ valuation q 76 = true := by
  rw [value34, value37, value57, value76, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(168 : Vertex), (224 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (164 : Vertex) [(168 : Vertex), (224 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 140 = true ∨ valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 76 = true := by
  rw [value34, value35, value37, value76, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(164 : Vertex), (168 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (224 : Vertex) [(164 : Vertex), (168 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 43 = true := by
  rw [value34, value35, value36, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ∈ [(160 : Vertex), (166 : Vertex), (180 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (164 : Vertex) [(160 : Vertex), (166 : Vertex), (180 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 141 = true ∨ valuation q 36 = true ∨ valuation q 43 = true := by
  rw [value35, value36, value43, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(166 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (160 : Vertex) [(166 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 141 = true ∨ valuation q 34 = true ∨ valuation q 43 = true := by
  rw [value34, value35, value43, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(160 : Vertex), (180 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (166 : Vertex) [(160 : Vertex), (180 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 45 = false := by
  rw [value35, value36, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (164 : Vertex) (174 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 142 = true ∨ valuation q 41 = true ∨ valuation q 45 = true := by
  rw [value36, value41, value45, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(174 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (164 : Vertex) [(174 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 142 = true ∨ valuation q 35 = true ∨ valuation q 45 = true := by
  rw [value35, value36, value45, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(164 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (174 : Vertex) [(164 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 142 = true ∨ valuation q 35 = true ∨ valuation q 41 = true := by
  rw [value35, value36, value41, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(164 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(164 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value34, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (169 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 47 = false := by
  rw [value34, value37, value38, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (169 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 58 = false := by
  rw [value37, value38, value39, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (169 : Vertex) (170 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 47 = false ∨ valuation q 58 = false := by
  rw [value37, value38, value47, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (169 : Vertex) (184 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 48 = false := by
  rw [value37, value38, value40, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (171 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 81 = false := by
  rw [value37, value38, value40, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (171 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 48 = false ∨ valuation q 81 = false := by
  rw [value37, value38, value48, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 48 = false ∨ valuation q 81 = false := by
  rw [value38, value40, value48, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (185 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value37, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (168 : Vertex) (171 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value37, value39, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (168 : Vertex) (174 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 49 = false := by
  rw [value39, value40, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (171 : Vertex) (174 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 145 = true ∨ valuation q 37 = true ∨ valuation q 40 = true ∨ valuation q 41 = true := by
  rw [value37, value39, value40, value41, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(168 : Vertex), (171 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (186 : Vertex) [(168 : Vertex), (171 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 40 = true := by
  rw [value40, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (171 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 50 = true := by
  rw [value38, value39, value40, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ∈ [(169 : Vertex), (170 : Vertex), (187 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (171 : Vertex) [(169 : Vertex), (170 : Vertex), (187 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value38, value39, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (171 : Vertex) (169 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide)

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 146 = true ∨ valuation q 39 = true ∨ valuation q 50 = true := by
  rw [value39, value40, value50, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(170 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (169 : Vertex) [(170 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 146 = true ∨ valuation q 38 = true ∨ valuation q 50 = true := by
  rw [value38, value40, value50, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(169 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (170 : Vertex) [(169 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 146 = true ∨ valuation q 38 = true ∨ valuation q 39 = true := by
  rw [value38, value39, value40, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(169 : Vertex), (170 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (187 : Vertex) [(169 : Vertex), (170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 59 = false := by
  rw [value36, value39, value41, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (170 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E091.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112091
