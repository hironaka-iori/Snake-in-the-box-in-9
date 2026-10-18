import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 115 = false := by
  rw [value45, value46, value47, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 49 = true := by
  rw [value45, value46, value48, value49, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(216 : Vertex), (219 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (201 : Vertex) [(216 : Vertex), (219 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 164 = true ∨ valuation q 38 = true ∨ valuation q 45 = true ∨ valuation q 48 = true := by
  rw [value38, value45, value46, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(201 : Vertex), (216 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (221 : Vertex) [(201 : Vertex), (216 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 29 = false ∨ valuation q 48 = false := by
  rw [value29, value48, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (218 : Vertex) (154 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 41 = true ∨ valuation q 45 = true ∨ valuation q 48 = true := by
  rw [value41, value45, value47, value48, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(210 : Vertex), (216 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (154 : Vertex) [(210 : Vertex), (216 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 29 = true ∨ valuation q 41 = true ∨ valuation q 48 = true := by
  rw [value29, value41, value47, value48, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(154 : Vertex), (210 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (216 : Vertex) [(154 : Vertex), (210 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 29 = true ∨ valuation q 41 = true ∨ valuation q 45 = true := by
  rw [value29, value41, value45, value47, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(154 : Vertex), (210 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (219 : Vertex) [(154 : Vertex), (210 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 166 = true ∨ valuation q 47 = true := by
  rw [value47, value48, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (217 : Vertex) [(218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 166 = true ∨ valuation q 46 = true := by
  rw [value46, value48, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 167 = true ∨ valuation q 46 = true := by
  rw [value46, value49, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (213 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 167 = true ∨ valuation q 42 = true := by
  rw [value42, value49, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (217 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value50, value51, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 65 = false := by
  rw [value50, value51, value52, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 81 = false := by
  rw [value50, value51, value52, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 65 = false := by
  rw [value50, value51, value55, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 81 = false := by
  rw [value50, value51, value55, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 65 = false ∨ valuation q 81 = false := by
  rw [value50, value51, value65, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 65 = false := by
  rw [value50, value52, value55, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (266 : Vertex) (274 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 81 = false := by
  rw [value50, value52, value55, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (266 : Vertex) (274 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 81 = false := by
  rw [value50, value52, value65, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (266 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 65 = false ∨ valuation q 81 = false := by
  rw [value50, value55, value65, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (274 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 168 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 65 = true ∨ valuation q 81 = true := by
  rw [value50, value52, value55, value65, value81, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(266 : Vertex), (274 : Vertex), (322 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (259 : Vertex) [(266 : Vertex), (274 : Vertex), (322 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 55 = true ∨ valuation q 65 = true ∨ valuation q 81 = true := by
  rw [value50, value51, value55, value65, value81, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(259 : Vertex), (274 : Vertex), (322 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(259 : Vertex), (274 : Vertex), (322 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value50, value51, value52, value55, value65, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(259 : Vertex), (266 : Vertex), (274 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (386 : Vertex) [(259 : Vertex), (266 : Vertex), (274 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = true ∨ valuation q 56 = true ∨ valuation q 82 = true := by
  rw [value50, value51, value56, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ∈ [(258 : Vertex), (275 : Vertex), (387 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (259 : Vertex) [(258 : Vertex), (275 : Vertex), (387 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 56 = true ∨ valuation q 82 = true := by
  rw [value51, value56, value82, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(275 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(275 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 82 = true := by
  rw [value50, value51, value82, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(258 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (275 : Vertex) [(258 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 56 = true := by
  rw [value50, value51, value56, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(258 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (387 : Vertex) [(258 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 52 = true := by
  rw [value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (266 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = true ∨ valuation q 70 = true ∨ valuation q 88 = true := by
  rw [value50, value52, value70, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ∈ [(258 : Vertex), (330 : Vertex), (394 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (266 : Vertex) [(258 : Vertex), (330 : Vertex), (394 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 70 = true ∨ valuation q 88 = true := by
  rw [value52, value70, value88, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(330 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(330 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 88 = true := by
  rw [value50, value52, value88, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(258 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (330 : Vertex) [(258 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E007.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112007
