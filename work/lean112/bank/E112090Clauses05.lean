import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 173 = true ∨ valuation q 61 = true ∨ valuation q 71 = true := by
  rw [value61, value64, value71, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(322 : Vertex), (342 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (324 : Vertex) [(322 : Vertex), (342 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 61 = false ∨ valuation q 66 = false ∨ valuation q 75 = false := by
  rw [value61, value65, value66, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (330 : Vertex) (322 : Vertex) (331 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 174 = true ∨ valuation q 61 = true ∨ valuation q 66 = true := by
  rw [value61, value65, value66, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(322 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (346 : Vertex) [(322 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 175 = true ∨ valuation q 49 = true ∨ valuation q 65 = true := by
  rw [value49, value65, value66, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(267 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (323 : Vertex) [(267 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 175 = true ∨ valuation q 49 = true ∨ valuation q 62 = true := by
  rw [value49, value62, value66, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(267 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (330 : Vertex) [(267 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 50 = false ∨ valuation q 63 = false ∨ valuation q 68 = false := by
  rw [value50, value63, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (324 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 176 = true ∨ valuation q 50 = true ∨ valuation q 68 = true := by
  rw [value50, value67, value68, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(268 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (324 : Vertex) [(268 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 177 = true ∨ valuation q 67 = true ∨ valuation q 76 = true := by
  rw [value67, value68, value76, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(332 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (269 : Vertex) [(332 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 76 = true := by
  rw [value51, value68, value76, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(269 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(269 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 177 = true ∨ valuation q 51 = true ∨ valuation q 67 = true := by
  rw [value51, value67, value68, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(269 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (349 : Vertex) [(269 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 54 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value54, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (337 : Vertex) (273 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 76 = false := by
  rw [value69, value70, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (341 : Vertex) (337 : Vertex) (343 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 179 = true ∨ valuation q 69 = true ∨ valuation q 76 = true := by
  rw [value69, value70, value76, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (341 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(337 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (341 : Vertex) (343 : Vertex) [(337 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 72 = true := by
  rw [value71, value72, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (326 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 180 = true ∨ valuation q 64 = true := by
  rw [value64, value71, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (343 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 181 = true ∨ valuation q 70 = true := by
  rw [value70, value72, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (343 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(341 : Vertex)] := by decide
  have hg := other_cover q (343 : Vertex) (342 : Vertex) [(341 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 182 = true ∨ valuation q 74 = true := by
  rw [value73, value74, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (344 : Vertex) w → w ∈ region → w ≠ (346 : Vertex) → w ∈ [(345 : Vertex)] := by decide
  have hg := other_cover q (344 : Vertex) (346 : Vertex) [(345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 69 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value69, value73, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (345 : Vertex) (337 : Vertex) (344 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 183 = true ∨ valuation q 69 = true ∨ valuation q 76 = true := by
  rw [value69, value74, value76, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(337 : Vertex), (349 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (344 : Vertex) [(337 : Vertex), (349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 184 = true ∨ valuation q 73 = true := by
  rw [value73, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(344 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (330 : Vertex) [(344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 184 = true ∨ valuation q 65 = true := by
  rw [value65, value75, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(330 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (344 : Vertex) [(330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 74 = false := by
  rw [value68, value70, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (333 : Vertex) (341 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 186 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(386 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (388 : Vertex) [(386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 12 = false ∨ valuation q 77 = false ∨ valuation q 82 = false := by
  rw [value12, value77, value78, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (384 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 12 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value12, value78, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 13 = false ∨ valuation q 45 = false ∨ valuation q 83 = false := by
  rw [value13, value45, value79, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 45 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value45, value78, value79, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 189 = true ∨ valuation q 81 = true ∨ valuation q 84 = true := by
  rw [value80, value81, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(390 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (384 : Vertex) [(390 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 189 = true ∨ valuation q 77 = true ∨ valuation q 84 = true := by
  rw [value77, value80, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(384 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (390 : Vertex) [(384 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 189 = true ∨ valuation q 77 = true ∨ valuation q 81 = true := by
  rw [value77, value80, value81, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (396 : Vertex) [(384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 88 = false := by
  rw [value78, value80, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (390 : Vertex) (386 : Vertex) (388 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 190 = true ∨ valuation q 78 = true ∨ valuation q 88 = true := by
  rw [value78, value81, value88, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (390 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(386 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (390 : Vertex) (388 : Vertex) [(386 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E090.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112090
