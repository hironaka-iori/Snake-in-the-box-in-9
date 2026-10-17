import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 155 = true ∨ valuation q 47 = true ∨ valuation q 50 = true := by
  rw [value47, value49, value50, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (170 : Vertex) → w ∈ [(184 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (170 : Vertex) [(184 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 155 = true ∨ valuation q 39 = true ∨ valuation q 50 = true := by
  rw [value39, value49, value50, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(170 : Vertex), (187 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (184 : Vertex) [(170 : Vertex), (187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 155 = true ∨ valuation q 39 = true ∨ valuation q 47 = true := by
  rw [value39, value47, value49, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (186 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(170 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (186 : Vertex) (187 : Vertex) [(170 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 48 = false := by
  rw [value40, value42, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (179 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 49 = false := by
  rw [value40, value42, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (179 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 63 = false := by
  rw [value40, value42, value50, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (179 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value40, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 48 = false ∨ valuation q 63 = false := by
  rw [value40, value48, value50, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (185 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 63 = false := by
  rw [value40, value49, value50, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (171 : Vertex) (186 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 42 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value42, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (179 : Vertex) (185 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 42 = false ∨ valuation q 48 = false ∨ valuation q 63 = false := by
  rw [value42, value48, value50, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (179 : Vertex) (185 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 42 = false ∨ valuation q 49 = false ∨ valuation q 63 = false := by
  rw [value42, value49, value50, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (179 : Vertex) (186 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 63 = false := by
  rw [value48, value49, value50, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (187 : Vertex) (185 : Vertex) (186 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 157 = true ∨ valuation q 48 = true := by
  rw [value48, value51, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (181 : Vertex) → w ∈ [(185 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (181 : Vertex) [(185 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 157 = true ∨ valuation q 44 = true := by
  rw [value44, value51, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (185 : Vertex) → w ∈ [(181 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (185 : Vertex) [(181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 158 = true ∨ valuation q 22 = true ∨ valuation q 58 = true ∨ valuation q 95 = true := by
  rw [value22, value52, value58, value95, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(72 : Vertex), (232 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (216 : Vertex) [(72 : Vertex), (232 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 158 = true ∨ valuation q 22 = true ∨ valuation q 54 = true ∨ valuation q 58 = true := by
  rw [value22, value52, value54, value58, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(72 : Vertex), (216 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (456 : Vertex) [(72 : Vertex), (216 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 53 = true := by
  rw [value53, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (203 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 56 = true := by
  rw [value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ∈ [(219 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (203 : Vertex) [(219 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 159 = true := by
  rw [value53, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (203 : Vertex) (219 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 160 = true ∨ valuation q 55 = true := by
  rw [value54, value55, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(218 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (200 : Vertex) [(218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 160 = true ∨ valuation q 52 = true := by
  rw [value52, value54, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(200 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (218 : Vertex) [(200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 55 = true := by
  rw [value55, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (218 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 54 = true ∨ valuation q 56 = true := by
  rw [value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ∈ [(216 : Vertex), (219 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (218 : Vertex) [(216 : Vertex), (219 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 161 = true ∨ valuation q 56 = true := by
  rw [value55, value56, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(219 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (216 : Vertex) [(219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 161 = true ∨ valuation q 54 = true := by
  rw [value54, value55, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(216 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (219 : Vertex) [(216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 30 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value30, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (91 : Vertex) (203 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 30 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value30, value53, value56, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (91 : Vertex) (203 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 30 = false ∨ valuation q 53 = false ∨ valuation q 103 = false := by
  rw [value30, value53, value56, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (91 : Vertex) (203 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 30 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value30, value55, value56, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (91 : Vertex) (218 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 30 = false ∨ valuation q 55 = false ∨ valuation q 103 = false := by
  rw [value30, value55, value56, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (91 : Vertex) (218 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 30 = false ∨ valuation q 63 = false ∨ valuation q 103 = false := by
  rw [value30, value56, value63, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (91 : Vertex) (251 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E091.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112091
