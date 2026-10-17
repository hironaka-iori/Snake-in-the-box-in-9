import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 146 = true ∨ valuation q 7 = true ∨ valuation q 19 = true ∨ valuation q 36 = true := by
  rw [value7, value18, value19, value36, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(12 : Vertex), (29 : Vertex), (92 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (284 : Vertex) [(12 : Vertex), (29 : Vertex), (92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value13, value16, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (21 : Vertex) (25 : Vertex) (28 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 20 = false := by
  rw [value13, value16, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (21 : Vertex) (25 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 13 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value13, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (21 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value16, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (25 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 13 = true ∨ valuation q 18 = true ∨ valuation q 20 = true := by
  rw [value13, value18, value19, value20, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(21 : Vertex), (28 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (25 : Vertex) [(21 : Vertex), (28 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 20 = true := by
  rw [value13, value16, value19, value20, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(21 : Vertex), (25 : Vertex), (31 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (28 : Vertex) [(21 : Vertex), (25 : Vertex), (31 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 147 = true ∨ valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 18 = true := by
  rw [value13, value16, value18, value19, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(21 : Vertex), (25 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (31 : Vertex) [(21 : Vertex), (25 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 91 = true := by
  rw [value9, value15, value17, value19, value20, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ∈ [(15 : Vertex), (23 : Vertex), (27 : Vertex), (29 : Vertex), (287 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (31 : Vertex) [(15 : Vertex), (23 : Vertex), (27 : Vertex), (29 : Vertex), (287 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 17 = false := by
  rw [value9, value15, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (23 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 19 = false := by
  rw [value9, value15, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (23 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 91 = false := by
  rw [value9, value17, value20, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (15 : Vertex) (27 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 91 = false := by
  rw [value15, value17, value20, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (23 : Vertex) (27 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 91 = false := by
  rw [value15, value19, value20, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (31 : Vertex) (23 : Vertex) (29 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 91 = true := by
  rw [value15, value17, value19, value20, value91, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (15 : Vertex) → w ∈ [(23 : Vertex), (27 : Vertex), (29 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (15 : Vertex) [(23 : Vertex), (27 : Vertex), (29 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 9 = true ∨ valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 91 = true := by
  rw [value9, value17, value19, value20, value91, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(15 : Vertex), (27 : Vertex), (29 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (23 : Vertex) [(15 : Vertex), (27 : Vertex), (29 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 9 = true ∨ valuation q 15 = true ∨ valuation q 19 = true ∨ valuation q 91 = true := by
  rw [value9, value15, value19, value20, value91, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(15 : Vertex), (23 : Vertex), (29 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (27 : Vertex) [(15 : Vertex), (23 : Vertex), (29 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 9 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 91 = true := by
  rw [value9, value15, value17, value20, value91, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(15 : Vertex), (23 : Vertex), (27 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (29 : Vertex) [(15 : Vertex), (23 : Vertex), (27 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 148 = true ∨ valuation q 9 = true ∨ valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 19 = true := by
  rw [value9, value15, value17, value19, value20, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(15 : Vertex), (23 : Vertex), (27 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (31 : Vertex) (287 : Vertex) [(15 : Vertex), (23 : Vertex), (27 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 21 = true := by
  rw [value21, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (67 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 25 = true ∨ valuation q 28 = true := by
  rw [value21, value25, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ∈ [(71 : Vertex), (75 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (67 : Vertex) [(71 : Vertex), (75 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 149 = true ∨ valuation q 28 = true := by
  rw [value21, value28, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (71 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 149 = true ∨ valuation q 25 = true := by
  rw [value21, value25, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(71 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (75 : Vertex) [(71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value22, value23, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (68 : Vertex) (69 : Vertex) (70 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 23 = true ∨ valuation q 32 = true := by
  rw [value22, value23, value32, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (70 : Vertex) → w ∈ [(69 : Vertex), (84 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (70 : Vertex) [(69 : Vertex), (84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 150 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value22, value23, value24, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (68 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(69 : Vertex), (70 : Vertex)] := by decide
  have hg := other_cover q (68 : Vertex) (84 : Vertex) [(69 : Vertex), (70 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 22 = false ∨ valuation q 59 = false := by
  rw [value4, value22, value23, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (68 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 25 = false ∨ valuation q 59 = false := by
  rw [value4, value23, value25, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (71 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 33 = false ∨ valuation q 59 = false := by
  rw [value4, value23, value33, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (85 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 4 = false ∨ valuation q 59 = false ∨ valuation q 95 = false := by
  rw [value4, value23, value59, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (5 : Vertex) (197 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 59 = false := by
  rw [value22, value23, value25, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (71 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 22 = false ∨ valuation q 33 = false ∨ valuation q 59 = false := by
  rw [value22, value23, value33, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (69 : Vertex) (68 : Vertex) (85 : Vertex) (197 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E055.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112055
