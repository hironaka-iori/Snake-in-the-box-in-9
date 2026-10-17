import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 24 = true ∨ valuation q 62 = true := by
  rw [value24, value25, value62, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(105 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (75 : Vertex) [(105 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 7 = true ∨ valuation q 62 = true := by
  rw [value7, value25, value62, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(75 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (105 : Vertex) [(75 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 7 = true ∨ valuation q 24 = true := by
  rw [value7, value24, value25, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(75 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (235 : Vertex) [(75 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = true ∨ valuation q 23 = true ∨ valuation q 27 = true ∨ valuation q 63 = true := by
  rw [value8, value23, value26, value27, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ∈ [(76 : Vertex), (104 : Vertex), (110 : Vertex), (236 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (108 : Vertex) [(76 : Vertex), (104 : Vertex), (110 : Vertex), (236 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 27 = false := by
  rw [value8, value23, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (108 : Vertex) (76 : Vertex) (104 : Vertex) (110 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 27 = false ∨ valuation q 63 = false := by
  rw [value8, value26, value27, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (108 : Vertex) (76 : Vertex) (110 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 23 = true ∨ valuation q 27 = true ∨ valuation q 63 = true := by
  rw [value23, value26, value27, value63, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(104 : Vertex), (110 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (76 : Vertex) [(104 : Vertex), (110 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 8 = true ∨ valuation q 27 = true ∨ valuation q 63 = true := by
  rw [value8, value26, value27, value63, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(76 : Vertex), (110 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (104 : Vertex) [(76 : Vertex), (110 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 8 = true ∨ valuation q 23 = true ∨ valuation q 63 = true := by
  rw [value8, value23, value26, value63, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (110 : Vertex) → w ∈ [(76 : Vertex), (104 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (110 : Vertex) [(76 : Vertex), (104 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 8 = true ∨ valuation q 23 = true ∨ valuation q 27 = true := by
  rw [value8, value23, value26, value27, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(76 : Vertex), (104 : Vertex), (110 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (236 : Vertex) [(76 : Vertex), (104 : Vertex), (110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 65 = false := by
  rw [value21, value26, value27, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (102 : Vertex) (108 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 21 = true ∨ valuation q 65 = true := by
  rw [value21, value27, value65, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(102 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (108 : Vertex) [(102 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 21 = true ∨ valuation q 26 = true := by
  rw [value21, value26, value27, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(102 : Vertex), (108 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (238 : Vertex) [(102 : Vertex), (108 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 28 = true := by
  rw [value28, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (113 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 11 = true ∨ valuation q 29 = true := by
  rw [value11, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ∈ [(81 : Vertex), (115 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (113 : Vertex) [(81 : Vertex), (115 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 11 = false ∨ valuation q 29 = false := by
  rw [value11, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (113 : Vertex) (81 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide)

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 29 = true := by
  rw [value28, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (81 : Vertex) → w ∈ [(115 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (81 : Vertex) [(115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 11 = true := by
  rw [value11, value28, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(81 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (115 : Vertex) [(81 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 67 = false := by
  rw [value12, value28, value29, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (83 : Vertex) (113 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 28 = true ∨ valuation q 67 = true := by
  rw [value28, value29, value67, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(113 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (83 : Vertex) [(113 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 12 = true ∨ valuation q 67 = true := by
  rw [value12, value29, value67, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(83 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (113 : Vertex) [(83 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 12 = true ∨ valuation q 28 = true := by
  rw [value12, value28, value29, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(83 : Vertex), (113 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (243 : Vertex) [(83 : Vertex), (113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 30 = true := by
  rw [value30, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (116 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 13 = true ∨ valuation q 31 = true := by
  rw [value13, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ∈ [(84 : Vertex), (118 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (116 : Vertex) [(84 : Vertex), (118 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 13 = false ∨ valuation q 31 = false := by
  rw [value13, value31, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (116 : Vertex) (84 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide)

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(118 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (84 : Vertex) [(118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 13 = true := by
  rw [value13, value30, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (118 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 21 = false ∨ valuation q 30 = false ∨ valuation q 69 = false := by
  rw [value21, value30, value31, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (118 : Vertex) (102 : Vertex) (116 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 21 = true ∨ valuation q 69 = true := by
  rw [value21, value31, value69, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(102 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (116 : Vertex) [(102 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 21 = true ∨ valuation q 30 = true := by
  rw [value21, value30, value31, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(102 : Vertex), (116 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (246 : Vertex) [(102 : Vertex), (116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 32 = true := by
  rw [value32, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (120 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 23 = false ∨ valuation q 33 = false ∨ valuation q 70 = false := by
  rw [value23, value32, value33, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (120 : Vertex) (104 : Vertex) (122 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E260.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112260
