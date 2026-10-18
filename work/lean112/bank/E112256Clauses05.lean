import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 26 = true := by
  rw [value25, value26, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(110 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (76 : Vertex) [(110 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 152 = true ∨ valuation q 8 = true := by
  rw [value8, value25, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (110 : Vertex) → w ∈ [(76 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (110 : Vertex) [(76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 25 = false ∨ valuation q 34 = false ∨ valuation q 62 = false := by
  rw [value25, value26, value34, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (110 : Vertex) (108 : Vertex) (126 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 34 = true ∨ valuation q 62 = true := by
  rw [value26, value34, value62, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(126 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (108 : Vertex) [(126 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 25 = true ∨ valuation q 34 = true := by
  rw [value25, value26, value34, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(108 : Vertex), (126 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (238 : Vertex) [(108 : Vertex), (126 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 28 = false := by
  rw [value10, value19, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (80 : Vertex) (96 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 30 = false := by
  rw [value10, value19, value27, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (80 : Vertex) (96 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 63 = false := by
  rw [value10, value19, value27, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (80 : Vertex) (96 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 10 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value10, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (80 : Vertex) (113 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 10 = false ∨ valuation q 28 = false ∨ valuation q 63 = false := by
  rw [value10, value27, value28, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (80 : Vertex) (113 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 10 = false ∨ valuation q 30 = false ∨ valuation q 63 = false := by
  rw [value10, value27, value30, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (80 : Vertex) (116 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value19, value27, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (113 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 63 = false := by
  rw [value19, value27, value28, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (113 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 19 = false ∨ valuation q 30 = false ∨ valuation q 63 = false := by
  rw [value19, value27, value30, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (96 : Vertex) (116 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 63 = false := by
  rw [value27, value28, value30, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (113 : Vertex) (116 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 10 = true ∨ valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 63 = true := by
  rw [value10, value27, value28, value30, value63, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (112 : Vertex) w → w ∈ region → w ≠ (96 : Vertex) → w ∈ [(80 : Vertex), (113 : Vertex), (116 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (112 : Vertex) (96 : Vertex) [(80 : Vertex), (113 : Vertex), (116 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 10 = true ∨ valuation q 19 = true ∨ valuation q 30 = true ∨ valuation q 63 = true := by
  rw [value10, value19, value27, value30, value63, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (112 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(80 : Vertex), (96 : Vertex), (116 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (112 : Vertex) (113 : Vertex) [(80 : Vertex), (96 : Vertex), (116 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 28 = true := by
  rw [value28, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (113 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 64 = true := by
  rw [value27, value28, value29, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ∈ [(112 : Vertex), (115 : Vertex), (241 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (113 : Vertex) [(112 : Vertex), (115 : Vertex), (241 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 29 = false ∨ valuation q 64 = false := by
  rw [value29, value64, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (113 : Vertex) (115 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 29 = true ∨ valuation q 64 = true := by
  rw [value28, value29, value64, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (112 : Vertex) → w ∈ [(115 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (112 : Vertex) [(115 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 27 = true ∨ valuation q 64 = true := by
  rw [value27, value28, value64, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(112 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (115 : Vertex) [(112 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value27, value28, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (241 : Vertex) → w ∈ [(112 : Vertex), (115 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (241 : Vertex) [(112 : Vertex), (115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 11 = false ∨ valuation q 28 = false ∨ valuation q 65 = false := by
  rw [value11, value28, value29, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (83 : Vertex) (113 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 28 = true ∨ valuation q 65 = true := by
  rw [value28, value29, value65, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(113 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (83 : Vertex) [(113 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 11 = true ∨ valuation q 65 = true := by
  rw [value11, value29, value65, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (113 : Vertex) → w ∈ [(83 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (113 : Vertex) [(83 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 11 = true ∨ valuation q 28 = true := by
  rw [value11, value28, value29, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(83 : Vertex), (113 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (243 : Vertex) [(83 : Vertex), (113 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 12 = true ∨ valuation q 27 = true ∨ valuation q 31 = true ∨ valuation q 66 = true := by
  rw [value12, value27, value30, value31, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ∈ [(84 : Vertex), (112 : Vertex), (118 : Vertex), (244 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (116 : Vertex) [(84 : Vertex), (112 : Vertex), (118 : Vertex), (244 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 12 = false ∨ valuation q 27 = false ∨ valuation q 66 = false := by
  rw [value12, value27, value30, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (84 : Vertex) (112 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 66 = false := by
  rw [value12, value30, value31, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (116 : Vertex) (84 : Vertex) (118 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 12 = false ∨ valuation q 31 = false := by
  rw [value12, value31, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (116 : Vertex) (84 : Vertex) (118 : Vertex) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 157 = true ∨ valuation q 27 = true ∨ valuation q 31 = true ∨ valuation q 66 = true := by
  rw [value27, value30, value31, value66, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(112 : Vertex), (118 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (84 : Vertex) [(112 : Vertex), (118 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E256.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112256
