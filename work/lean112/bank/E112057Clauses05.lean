import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 12 = true ∨ valuation q 20 = true ∨ valuation q 88 = true := by
  rw [value12, value17, value20, value88, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(19 : Vertex), (31 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (25 : Vertex) [(19 : Vertex), (31 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 88 = true := by
  rw [value12, value16, value17, value88, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(19 : Vertex), (25 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (31 : Vertex) [(19 : Vertex), (25 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 144 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 20 = true := by
  rw [value12, value16, value17, value20, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(19 : Vertex), (25 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (283 : Vertex) [(19 : Vertex), (25 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 7 = false ∨ valuation q 19 = false ∨ valuation q 36 = false := by
  rw [value7, value18, value19, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (12 : Vertex) (29 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 7 = false ∨ valuation q 19 = false ∨ valuation q 89 = false := by
  rw [value7, value18, value19, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (12 : Vertex) (29 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 7 = false ∨ valuation q 36 = false ∨ valuation q 89 = false := by
  rw [value7, value18, value36, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (12 : Vertex) (92 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 36 = false ∨ valuation q 89 = false := by
  rw [value18, value19, value36, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (29 : Vertex) (92 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 7 = false ∨ valuation q 19 = false := by
  rw [value7, value19, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (28 : Vertex) (12 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 19 = true ∨ valuation q 36 = true ∨ valuation q 89 = true := by
  rw [value18, value19, value36, value89, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(29 : Vertex), (92 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (12 : Vertex) [(29 : Vertex), (92 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 7 = true ∨ valuation q 36 = true ∨ valuation q 89 = true := by
  rw [value7, value18, value36, value89, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(12 : Vertex), (92 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(12 : Vertex), (92 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 145 = true ∨ valuation q 7 = true ∨ valuation q 19 = true ∨ valuation q 36 = true := by
  rw [value7, value18, value19, value36, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(12 : Vertex), (29 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (284 : Vertex) [(12 : Vertex), (29 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value13, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (21 : Vertex) (25 : Vertex) (28 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value13, value16, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (21 : Vertex) (25 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value13, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (21 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value16, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (25 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 20 = true := by
  rw [value16, value18, value19, value20, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(25 : Vertex), (28 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (21 : Vertex) [(25 : Vertex), (28 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 13 = true ∨ valuation q 18 = true ∨ valuation q 20 = true := by
  rw [value13, value18, value19, value20, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(21 : Vertex), (28 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (25 : Vertex) [(21 : Vertex), (28 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 20 = true := by
  rw [value13, value16, value19, value20, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(21 : Vertex), (25 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (28 : Vertex) [(21 : Vertex), (25 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 146 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 18 = true := by
  rw [value13, value16, value18, value19, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(21 : Vertex), (25 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (31 : Vertex) [(21 : Vertex), (25 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value9, value15, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (23 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value9, value15, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (23 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 90 = false := by
  rw [value9, value15, value20, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (23 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value9, value17, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 90 = false := by
  rw [value9, value17, value20, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value15, value17, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (23 : Vertex) (27 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 90 = false := by
  rw [value15, value17, value20, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (23 : Vertex) (27 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 90 = false := by
  rw [value15, value19, value20, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (23 : Vertex) (29 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 90 = false := by
  rw [value17, value19, value20, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (27 : Vertex) (29 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value15, value19, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (31 : Vertex) (23 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 147 = true ∨ valuation q 9 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 90 = true := by
  rw [value9, value15, value19, value20, value90, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(15 : Vertex), (23 : Vertex), (29 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (27 : Vertex) [(15 : Vertex), (23 : Vertex), (29 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 94 = false := by
  rw [value21, value25, value28, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (323 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 25 = false ∨ valuation q 28 = false := by
  rw [value25, value28, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E057.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112057
