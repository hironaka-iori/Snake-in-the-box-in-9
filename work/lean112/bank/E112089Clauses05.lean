import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 35 = true ∨ valuation q 68 = true := by
  rw [value27, value35, value68, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(95 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (78 : Vertex) [(95 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 26 = true ∨ valuation q 68 = true := by
  rw [value26, value27, value68, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(78 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (95 : Vertex) [(78 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 151 = true ∨ valuation q 26 = true ∨ valuation q 35 = true := by
  rw [value26, value27, value35, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(78 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (207 : Vertex) [(78 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 13 = false ∨ valuation q 31 = false ∨ valuation q 34 = false := by
  rw [value13, value28, value31, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (87 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 13 = false ∨ valuation q 31 = false ∨ valuation q 72 = false := by
  rw [value13, value28, value31, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (87 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 13 = false ∨ valuation q 34 = false ∨ valuation q 72 = false := by
  rw [value13, value28, value34, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (19 : Vertex) (91 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 72 = false := by
  rw [value28, value31, value34, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (83 : Vertex) (87 : Vertex) (91 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 152 = true ∨ valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 72 = true := by
  rw [value28, value31, value34, value72, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(87 : Vertex), (91 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (19 : Vertex) [(87 : Vertex), (91 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 152 = true ∨ valuation q 13 = true ∨ valuation q 34 = true ∨ valuation q 72 = true := by
  rw [value13, value28, value34, value72, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(19 : Vertex), (91 : Vertex), (211 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (87 : Vertex) [(19 : Vertex), (91 : Vertex), (211 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 29 = true := by
  rw [value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (84 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 21 = true ∨ valuation q 30 = true := by
  rw [value21, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ∈ [(68 : Vertex), (85 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (84 : Vertex) [(68 : Vertex), (85 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 21 = false ∨ valuation q 30 = false := by
  rw [value21, value30, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (84 : Vertex) (68 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 30 = true := by
  rw [value29, value30, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 153 = true ∨ valuation q 21 = true := by
  rw [value21, value29, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(68 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (85 : Vertex) [(68 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 154 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (84 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 154 = true ∨ valuation q 29 = true := by
  rw [value29, value30, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (87 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 31 = true := by
  rw [value31, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (87 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value28, value30, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ∈ [(83 : Vertex), (85 : Vertex), (95 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (87 : Vertex) [(83 : Vertex), (85 : Vertex), (95 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 35 = false := by
  rw [value28, value30, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (87 : Vertex) (83 : Vertex) (85 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value30, value31, value35, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(85 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (83 : Vertex) [(85 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 28 = true ∨ valuation q 35 = true := by
  rw [value28, value31, value35, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(83 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (85 : Vertex) [(83 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 155 = true ∨ valuation q 28 = true ∨ valuation q 30 = true := by
  rw [value28, value30, value31, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(83 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (95 : Vertex) [(83 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 32 = true := by
  rw [value32, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (88 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 23 = true ∨ valuation q 33 = true ∨ valuation q 74 = true := by
  rw [value23, value32, value33, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (90 : Vertex), (216 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (88 : Vertex) [(72 : Vertex), (90 : Vertex), (216 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 23 = false ∨ valuation q 33 = false ∨ valuation q 74 = false := by
  rw [value23, value32, value33, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (90 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 23 = false ∨ valuation q 33 = false := by
  rw [value23, value33, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (88 : Vertex) (72 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 23 = false ∨ valuation q 74 = false := by
  rw [value23, value74, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (88 : Vertex) (72 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 33 = true ∨ valuation q 74 = true := by
  rw [value32, value33, value74, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(90 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (72 : Vertex) [(90 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 23 = true ∨ valuation q 74 = true := by
  rw [value23, value32, value74, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(72 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (90 : Vertex) [(72 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 156 = true ∨ valuation q 23 = true ∨ valuation q 33 = true := by
  rw [value23, value32, value33, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(72 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (216 : Vertex) [(72 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 75 = false := by
  rw [value32, value33, value34, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (88 : Vertex) (91 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 157 = true ∨ valuation q 34 = true ∨ valuation q 75 = true := by
  rw [value33, value34, value75, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(91 : Vertex), (218 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (88 : Vertex) [(91 : Vertex), (218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E089.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112089
