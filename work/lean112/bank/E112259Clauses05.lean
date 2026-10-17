import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 32 = false ∨ valuation q 48 = false ∨ valuation q 87 = false := by
  rw [value28, value32, value48, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (49 : Vertex) (57 : Vertex) (113 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 11 = false ∨ valuation q 27 = false ∨ valuation q 88 = false := by
  rw [value11, value27, value29, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (50 : Vertex) (18 : Vertex) (48 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 11 = false ∨ valuation q 27 = false := by
  rw [value11, value27, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (50 : Vertex) (18 : Vertex) (48 : Vertex) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 11 = false ∨ valuation q 88 = false := by
  rw [value11, value88, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (50 : Vertex) (18 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 27 = true ∨ valuation q 88 = true := by
  rw [value27, value29, value88, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(48 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (18 : Vertex) [(48 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 11 = true ∨ valuation q 88 = true := by
  rw [value11, value29, value88, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (48 : Vertex) → w ∈ [(18 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (48 : Vertex) [(18 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 145 = true ∨ valuation q 11 = true ∨ valuation q 27 = true := by
  rw [value11, value27, value29, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (50 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(18 : Vertex), (48 : Vertex)] := by decide
  have hg := other_cover q (50 : Vertex) (178 : Vertex) [(18 : Vertex), (48 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value12, value28, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (21 : Vertex) (49 : Vertex) (55 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 90 = false := by
  rw [value12, value28, value30, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (21 : Vertex) (49 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 90 = false := by
  rw [value28, value30, value31, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (53 : Vertex) (49 : Vertex) (55 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 90 = true := by
  rw [value28, value30, value31, value90, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(49 : Vertex), (55 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (21 : Vertex) [(49 : Vertex), (55 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 12 = true ∨ valuation q 31 = true ∨ valuation q 90 = true := by
  rw [value12, value30, value31, value90, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(21 : Vertex), (55 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (49 : Vertex) [(21 : Vertex), (55 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 12 = true ∨ valuation q 28 = true ∨ valuation q 90 = true := by
  rw [value12, value28, value30, value90, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(21 : Vertex), (49 : Vertex), (181 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (55 : Vertex) [(21 : Vertex), (49 : Vertex), (181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 146 = true ∨ valuation q 12 = true ∨ valuation q 28 = true ∨ valuation q 31 = true := by
  rw [value12, value28, value30, value31, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (53 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(21 : Vertex), (49 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (53 : Vertex) (181 : Vertex) [(21 : Vertex), (49 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = true ∨ valuation q 91 = true := by
  rw [value30, value31, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ∈ [(53 : Vertex), (183 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (55 : Vertex) [(53 : Vertex), (183 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 30 = false ∨ valuation q 91 = false := by
  rw [value30, value91, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (55 : Vertex) (53 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 91 = true := by
  rw [value31, value91, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(183 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (53 : Vertex) [(183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 147 = true ∨ valuation q 30 = true := by
  rw [value30, value31, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (55 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(53 : Vertex)] := by decide
  have hg := other_cover q (55 : Vertex) (183 : Vertex) [(53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 92 = false := by
  rw [value28, value32, value33, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (57 : Vertex) (49 : Vertex) (59 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 33 = true ∨ valuation q 92 = true := by
  rw [value32, value33, value92, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(59 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (49 : Vertex) [(59 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 28 = true ∨ valuation q 92 = true := by
  rw [value28, value32, value92, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(49 : Vertex), (185 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (59 : Vertex) [(49 : Vertex), (185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 28 = true ∨ valuation q 33 = true := by
  rw [value28, value32, value33, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (57 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(49 : Vertex), (59 : Vertex)] := by decide
  have hg := other_cover q (57 : Vertex) (185 : Vertex) [(49 : Vertex), (59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 149 = true ∨ valuation q 32 = true := by
  rw [value32, value33, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(57 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (27 : Vertex) [(57 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 149 = true ∨ valuation q 15 = true := by
  rw [value15, value33, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (59 : Vertex) w → w ∈ region → w ≠ (57 : Vertex) → w ∈ [(27 : Vertex)] := by decide
  have hg := other_cover q (59 : Vertex) (57 : Vertex) [(27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 35 = true := by
  rw [value34, value35, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (60 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(62 : Vertex)] := by decide
  have hg := other_cover q (60 : Vertex) (28 : Vertex) [(62 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 150 = true ∨ valuation q 16 = true := by
  rw [value16, value34, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (60 : Vertex) w → w ∈ region → w ≠ (62 : Vertex) → w ∈ [(28 : Vertex)] := by decide
  have hg := other_cover q (60 : Vertex) (62 : Vertex) [(28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 17 = false ∨ valuation q 34 = false ∨ valuation q 95 = false := by
  rw [value17, value34, value35, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (62 : Vertex) (30 : Vertex) (60 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 17 = false ∨ valuation q 95 = false := by
  rw [value17, value95, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (62 : Vertex) (30 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 151 = true ∨ valuation q 34 = true ∨ valuation q 95 = true := by
  rw [value34, value35, value95, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(60 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (30 : Vertex) [(60 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 151 = true ∨ valuation q 17 = true ∨ valuation q 95 = true := by
  rw [value17, value35, value95, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (60 : Vertex) → w ∈ [(30 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (60 : Vertex) [(30 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 151 = true ∨ valuation q 17 = true ∨ valuation q 34 = true := by
  rw [value17, value34, value35, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (62 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(30 : Vertex), (60 : Vertex)] := by decide
  have hg := other_cover q (62 : Vertex) (190 : Vertex) [(30 : Vertex), (60 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 152 = true ∨ valuation q 45 = true := by
  rw [value36, value45, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(107 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (79 : Vertex) [(107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E259.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112259
