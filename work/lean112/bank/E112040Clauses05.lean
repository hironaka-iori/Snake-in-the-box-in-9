import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 29 = false ∨ valuation q 65 = false := by
  rw [value8, value26, value29, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (111 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 29 = false ∨ valuation q 100 = false := by
  rw [value8, value26, value29, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (111 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 65 = false ∨ valuation q 100 = false := by
  rw [value8, value26, value65, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (235 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 65 = false := by
  rw [value23, value25, value26, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (99 : Vertex) (105 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 29 = false ∨ valuation q 65 = false := by
  rw [value23, value26, value29, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (99 : Vertex) (111 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 23 = false ∨ valuation q 65 = false ∨ valuation q 100 = false := by
  rw [value23, value26, value65, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (99 : Vertex) (235 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 25 = false ∨ valuation q 29 = false ∨ valuation q 65 = false := by
  rw [value25, value26, value29, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (105 : Vertex) (111 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 29 = false ∨ valuation q 65 = false ∨ valuation q 100 = false := by
  rw [value26, value29, value65, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (111 : Vertex) (235 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 146 = true ∨ valuation q 23 = true ∨ valuation q 25 = true ∨ valuation q 29 = true ∨ valuation q 65 = true ∨ valuation q 100 = true := by
  rw [value23, value25, value26, value29, value65, value100, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (43 : Vertex) → w ∈ [(99 : Vertex), (105 : Vertex), (111 : Vertex), (235 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (43 : Vertex) [(99 : Vertex), (105 : Vertex), (111 : Vertex), (235 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 146 = true ∨ valuation q 8 = true ∨ valuation q 23 = true ∨ valuation q 25 = true ∨ valuation q 29 = true ∨ valuation q 100 = true := by
  rw [value8, value23, value25, value26, value29, value100, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(43 : Vertex), (99 : Vertex), (105 : Vertex), (111 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (235 : Vertex) [(43 : Vertex), (99 : Vertex), (105 : Vertex), (111 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 9 = false ∨ valuation q 28 = false ∨ valuation q 39 = false := by
  rw [value9, value27, value28, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (108 : Vertex) (44 : Vertex) (109 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 28 = false ∨ valuation q 39 = false := by
  rw [value28, value39, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (108 : Vertex) (109 : Vertex) (124 : Vertex) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 147 = true ∨ valuation q 28 = true ∨ valuation q 39 = true := by
  rw [value27, value28, value39, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (44 : Vertex) → w ∈ [(109 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (44 : Vertex) [(109 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 147 = true ∨ valuation q 9 = true ∨ valuation q 39 = true := by
  rw [value9, value27, value39, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(44 : Vertex), (124 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (109 : Vertex) [(44 : Vertex), (124 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 147 = true ∨ valuation q 9 = true ∨ valuation q 28 = true := by
  rw [value9, value27, value28, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ≠ (124 : Vertex) → w ∈ [(44 : Vertex), (109 : Vertex)] := by decide
  have hg := other_cover q (108 : Vertex) (124 : Vertex) [(44 : Vertex), (109 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value25, value27, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (105 : Vertex) (108 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 40 = false := by
  rw [value25, value27, value28, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (105 : Vertex) (108 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 25 = false ∨ valuation q 29 = false ∨ valuation q 40 = false := by
  rw [value25, value28, value29, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (105 : Vertex) (111 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 40 = false := by
  rw [value27, value28, value29, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (109 : Vertex) (108 : Vertex) (111 : Vertex) (125 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 148 = true ∨ valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 40 = true := by
  rw [value27, value28, value29, value40, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(108 : Vertex), (111 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (105 : Vertex) [(108 : Vertex), (111 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 148 = true ∨ valuation q 25 = true ∨ valuation q 29 = true ∨ valuation q 40 = true := by
  rw [value25, value28, value29, value40, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(105 : Vertex), (111 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (108 : Vertex) [(105 : Vertex), (111 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 148 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 40 = true := by
  rw [value25, value27, value28, value40, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (111 : Vertex) → w ∈ [(105 : Vertex), (108 : Vertex), (125 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (111 : Vertex) [(105 : Vertex), (108 : Vertex), (125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 148 = true ∨ valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value25, value27, value28, value29, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(105 : Vertex), (108 : Vertex), (111 : Vertex)] := by decide
  have hg := other_cover q (109 : Vertex) (125 : Vertex) [(105 : Vertex), (108 : Vertex), (111 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value24, value26, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (103 : Vertex) (107 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 42 = false := by
  rw [value24, value26, value29, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (103 : Vertex) (107 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 24 = false ∨ valuation q 28 = false ∨ valuation q 42 = false := by
  rw [value24, value28, value29, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (103 : Vertex) (109 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 42 = false := by
  rw [value26, value28, value29, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (111 : Vertex) (107 : Vertex) (109 : Vertex) (127 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 149 = true ∨ valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 42 = true := by
  rw [value26, value28, value29, value42, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (103 : Vertex) → w ∈ [(107 : Vertex), (109 : Vertex), (127 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (103 : Vertex) [(107 : Vertex), (109 : Vertex), (127 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 149 = true ∨ valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 42 = true := by
  rw [value24, value26, value29, value42, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (111 : Vertex) w → w ∈ region → w ≠ (109 : Vertex) → w ∈ [(103 : Vertex), (107 : Vertex), (127 : Vertex)] := by decide
  have hg := other_cover q (111 : Vertex) (109 : Vertex) [(103 : Vertex), (107 : Vertex), (127 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 20 = false ∨ valuation q 31 = false := by
  rw [value11, value20, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (114 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 20 = false ∨ valuation q 33 = false := by
  rw [value11, value20, value30, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (116 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 11 = false ∨ valuation q 20 = false ∨ valuation q 36 = false := by
  rw [value11, value20, value30, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (112 : Vertex) (48 : Vertex) (96 : Vertex) (120 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E040.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112040
