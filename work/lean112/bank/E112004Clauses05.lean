import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 155 = true ∨ valuation q 37 = true ∨ valuation q 39 = true := by
  rw [value35, value37, value39, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(163 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 155 = true ∨ valuation q 34 = true ∨ valuation q 39 = true := by
  rw [value34, value35, value39, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(160 : Vertex), (169 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (163 : Vertex) [(160 : Vertex), (169 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 155 = true ∨ valuation q 34 = true ∨ valuation q 37 = true := by
  rw [value34, value35, value37, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (169 : Vertex) [(160 : Vertex), (163 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 45 = true ∨ valuation q 57 = true := by
  rw [value34, value36, value37, value45, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ∈ [(160 : Vertex), (163 : Vertex), (178 : Vertex), (226 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (162 : Vertex) [(160 : Vertex), (163 : Vertex), (178 : Vertex), (226 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 45 = false ∨ valuation q 57 = false := by
  rw [value36, value37, value45, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (163 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 156 = true ∨ valuation q 37 = true ∨ valuation q 45 = true ∨ valuation q 57 = true := by
  rw [value36, value37, value45, value57, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(163 : Vertex), (178 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 156 = true ∨ valuation q 34 = true ∨ valuation q 45 = true ∨ valuation q 57 = true := by
  rw [value34, value36, value45, value57, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(160 : Vertex), (178 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (163 : Vertex) [(160 : Vertex), (178 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 156 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 57 = true := by
  rw [value34, value36, value37, value57, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (178 : Vertex) [(160 : Vertex), (163 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 156 = true ∨ valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 45 = true := by
  rw [value34, value36, value37, value45, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (226 : Vertex) [(160 : Vertex), (163 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value35, value36, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (167 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value35, value36, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 46 = false := by
  rw [value35, value36, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value35, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (167 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 46 = false := by
  rw [value35, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (167 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 35 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value35, value37, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 40 = false := by
  rw [value36, value37, value38, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (167 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 46 = false := by
  rw [value36, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (167 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value36, value37, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 46 = false := by
  rw [value37, value38, value40, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (167 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 88 = false := by
  rw [value37, value38, value43, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (163 : Vertex) (175 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 37 = false ∨ valuation q 49 = false ∨ valuation q 88 = false := by
  rw [value37, value38, value49, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (163 : Vertex) (183 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 43 = false ∨ valuation q 49 = false ∨ valuation q 88 = false := by
  rw [value38, value43, value49, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (167 : Vertex) (175 : Vertex) (183 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 43 = true ∨ valuation q 49 = true ∨ valuation q 88 = true := by
  rw [value38, value43, value49, value88, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(175 : Vertex), (183 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (163 : Vertex) [(175 : Vertex), (183 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 37 = true ∨ valuation q 49 = true ∨ valuation q 88 = true := by
  rw [value37, value38, value49, value88, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex), (183 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (175 : Vertex) [(163 : Vertex), (183 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 37 = true ∨ valuation q 43 = true ∨ valuation q 88 = true := by
  rw [value37, value38, value43, value88, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (183 : Vertex) [(163 : Vertex), (175 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 158 = true ∨ valuation q 37 = true ∨ valuation q 43 = true ∨ valuation q 49 = true := by
  rw [value37, value38, value43, value49, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (167 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex), (183 : Vertex)] := by decide
  have hg := other_cover q (167 : Vertex) (423 : Vertex) [(163 : Vertex), (175 : Vertex), (183 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 39 = true := by
  rw [value39, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (169 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 35 = false ∨ valuation q 40 = false := by
  rw [value5, value35, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (161 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value5, value35, value39, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (161 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 35 = false ∨ valuation q 51 = false := by
  rw [value5, value35, value39, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (161 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 35 = false ∨ valuation q 61 = false := by
  rw [value5, value35, value39, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (161 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 5 = false ∨ valuation q 35 = false ∨ valuation q 90 = false := by
  rw [value5, value35, value39, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (41 : Vertex) (161 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E004.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112004
