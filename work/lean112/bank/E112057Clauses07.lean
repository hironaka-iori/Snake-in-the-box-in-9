import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 5 = false ∨ valuation q 27 = false ∨ valuation q 34 = false := by
  rw [value5, value26, value27, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (8 : Vertex) (73 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 27 = true ∨ valuation q 34 = true := by
  rw [value26, value27, value34, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (8 : Vertex) → w ∈ [(73 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (8 : Vertex) [(73 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 5 = true ∨ valuation q 34 = true := by
  rw [value5, value26, value34, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(8 : Vertex), (88 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (73 : Vertex) [(8 : Vertex), (88 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 153 = true ∨ valuation q 5 = true ∨ valuation q 27 = true := by
  rw [value5, value26, value27, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (88 : Vertex) → w ∈ [(8 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (72 : Vertex) (88 : Vertex) [(8 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 26 = true ∨ valuation q 28 = true := by
  rw [value26, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (75 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (73 : Vertex) [(72 : Vertex), (75 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value26, value28, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (73 : Vertex) (72 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 28 = true := by
  rw [value27, value28, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (72 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 154 = true ∨ valuation q 26 = true := by
  rw [value26, value27, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(72 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (75 : Vertex) [(72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value27, value28, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (67 : Vertex) → w ∈ [(73 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (67 : Vertex) [(73 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 21 = true ∨ valuation q 29 = true := by
  rw [value21, value28, value29, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (73 : Vertex) → w ∈ [(67 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (73 : Vertex) [(67 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 155 = true ∨ valuation q 21 = true ∨ valuation q 27 = true := by
  rw [value21, value27, value28, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(67 : Vertex), (73 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (79 : Vertex) [(67 : Vertex), (73 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 9 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value9, value25, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (15 : Vertex) (71 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value25, value28, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 156 = true ∨ valuation q 9 = true ∨ valuation q 25 = true := by
  rw [value9, value25, value29, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(15 : Vertex), (71 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (75 : Vertex) [(15 : Vertex), (71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value30, value31, value32, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (82 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 63 = false := by
  rw [value30, value31, value32, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (82 : Vertex) (84 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 63 = false ∨ valuation q 100 = false := by
  rw [value30, value31, value63, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (82 : Vertex) (208 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 63 = false := by
  rw [value30, value32, value34, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (208 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 100 = false := by
  rw [value30, value32, value34, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (336 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 35 = false := by
  rw [value11, value30, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (82 : Vertex) (18 : Vertex) (80 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 11 = false ∨ valuation q 30 = false := by
  rw [value11, value30, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (82 : Vertex) (18 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 11 = false ∨ valuation q 35 = false := by
  rw [value11, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (82 : Vertex) (18 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value30, value31, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(80 : Vertex), (90 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (18 : Vertex) [(80 : Vertex), (90 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 158 = true ∨ valuation q 11 = true ∨ valuation q 30 = true := by
  rw [value11, value30, value31, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (82 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(18 : Vertex), (80 : Vertex)] := by decide
  have hg := other_cover q (82 : Vertex) (90 : Vertex) [(18 : Vertex), (80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 33 = false := by
  rw [value22, value30, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 22 = false ∨ valuation q 30 = false ∨ valuation q 36 = false := by
  rw [value22, value30, value32, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 22 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value22, value32, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (68 : Vertex) (85 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value30, value32, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (84 : Vertex) (80 : Vertex) (85 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 22 = false ∨ valuation q 30 = false := by
  rw [value22, value30, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (84 : Vertex) (68 : Vertex) (80 : Vertex) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value30, value32, value33, value36, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(80 : Vertex), (85 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (68 : Vertex) [(80 : Vertex), (85 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 159 = true ∨ valuation q 22 = true ∨ valuation q 30 = true ∨ valuation q 33 = true := by
  rw [value22, value30, value32, value33, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (92 : Vertex) → w ∈ [(68 : Vertex), (80 : Vertex), (85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (92 : Vertex) [(68 : Vertex), (80 : Vertex), (85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 160 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value23, value32, value33, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (85 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (85 : Vertex) (21 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E057.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112057
