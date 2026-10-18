import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 34 = false ∨ valuation q 64 = false ∨ valuation q 100 = false := by
  rw [value30, value34, value64, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (88 : Vertex) (208 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 64 = true ∨ valuation q 100 = true := by
  rw [value30, value32, value34, value64, value100, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(84 : Vertex), (88 : Vertex), (208 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (82 : Vertex) [(84 : Vertex), (88 : Vertex), (208 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 158 = true ∨ valuation q 31 = true ∨ valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 100 = true := by
  rw [value30, value31, value32, value34, value100, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(82 : Vertex), (84 : Vertex), (88 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (208 : Vertex) [(82 : Vertex), (84 : Vertex), (88 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 31 = true := by
  rw [value31, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (82 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 11 = false ∨ valuation q 35 = false := by
  rw [value11, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (82 : Vertex) (18 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value30, value31, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(80 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (18 : Vertex) [(80 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 11 = true ∨ valuation q 35 = true := by
  rw [value11, value31, value35, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(18 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (80 : Vertex) [(18 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 159 = true ∨ valuation q 11 = true ∨ valuation q 30 = true := by
  rw [value11, value30, value31, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(18 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (90 : Vertex) [(18 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 22 = true ∨ valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value22, value30, value32, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ∈ [(68 : Vertex), (80 : Vertex), (85 : Vertex), (92 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (84 : Vertex) [(68 : Vertex), (80 : Vertex), (85 : Vertex), (92 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value22, value30, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 36 = false := by
  rw [value22, value30, value32, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value30, value32, value33, value36, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(80 : Vertex), (85 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(80 : Vertex), (85 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 22 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value22, value32, value33, value36, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(68 : Vertex), (85 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(68 : Vertex), (85 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 22 = true ∨ valuation q 30 = true ∨ valuation q 36 = true := by
  rw [value22, value30, value32, value36, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (85 : Vertex) → w ∈ [(68 : Vertex), (80 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (85 : Vertex) [(68 : Vertex), (80 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 160 = true ∨ valuation q 22 = true ∨ valuation q 30 = true ∨ valuation q 33 = true := by
  rw [value22, value30, value32, value33, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(68 : Vertex), (80 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (92 : Vertex) [(68 : Vertex), (80 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 161 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value23, value32, value33, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (21 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 161 = true ∨ valuation q 13 = true ∨ valuation q 23 = true := by
  rw [value13, value23, value33, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(21 : Vertex), (69 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (84 : Vertex) [(21 : Vertex), (69 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 36 = false := by
  rw [value26, value30, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (80 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value26, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (72 : Vertex) (90 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 30 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value30, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (88 : Vertex) (80 : Vertex) (90 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 162 = true ∨ valuation q 30 = true ∨ valuation q 35 = true ∨ valuation q 36 = true := by
  rw [value30, value34, value35, value36, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(80 : Vertex), (90 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (72 : Vertex) [(80 : Vertex), (90 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 162 = true ∨ valuation q 26 = true ∨ valuation q 35 = true ∨ valuation q 36 = true := by
  rw [value26, value34, value35, value36, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(72 : Vertex), (90 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (80 : Vertex) [(72 : Vertex), (90 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 162 = true ∨ valuation q 26 = true ∨ valuation q 30 = true ∨ valuation q 36 = true := by
  rw [value26, value30, value34, value36, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (88 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(72 : Vertex), (80 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (88 : Vertex) (90 : Vertex) [(72 : Vertex), (80 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value31, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (90 : Vertex) (82 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value34, value35, value37, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (82 : Vertex) → w ∈ [(88 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (82 : Vertex) [(88 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 31 = true ∨ valuation q 37 = true := by
  rw [value31, value35, value37, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(82 : Vertex), (94 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (88 : Vertex) [(82 : Vertex), (94 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 163 = true ∨ valuation q 31 = true ∨ valuation q 34 = true := by
  rw [value31, value34, value35, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (90 : Vertex) w → w ∈ region → w ≠ (94 : Vertex) → w ∈ [(82 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (90 : Vertex) (94 : Vertex) [(82 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value18, value32, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 37 = false := by
  rw [value18, value32, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (84 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 106 = false := by
  rw [value18, value32, value36, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (84 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value18, value34, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (88 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 106 = false := by
  rw [value18, value34, value36, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (28 : Vertex) (88 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E055.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112055
