import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 55 = false := by
  rw [value49, value50, value51, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (196 : Vertex) (197 : Vertex) (198 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 173 = true ∨ valuation q 14 = true ∨ valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 55 = true := by
  rw [value14, value47, value49, value50, value51, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(68 : Vertex), (192 : Vertex), (197 : Vertex), (198 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (132 : Vertex) [(68 : Vertex), (192 : Vertex), (197 : Vertex), (198 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 173 = true ∨ valuation q 14 = true ∨ valuation q 32 = true ∨ valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 55 = true := by
  rw [value14, value32, value49, value50, value51, value55, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (196 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(68 : Vertex), (132 : Vertex), (197 : Vertex), (198 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (196 : Vertex) (192 : Vertex) [(68 : Vertex), (132 : Vertex), (197 : Vertex), (198 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 33 = false ∨ valuation q 49 = false ∨ valuation q 60 = false := by
  rw [value33, value49, value50, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (196 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 33 = false ∨ valuation q 49 = false ∨ valuation q 106 = false := by
  rw [value33, value49, value50, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (196 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 33 = false ∨ valuation q 60 = false ∨ valuation q 106 = false := by
  rw [value33, value50, value60, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (133 : Vertex) (213 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 106 = false := by
  rw [value49, value50, value60, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (196 : Vertex) (213 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 174 = true ∨ valuation q 33 = true ∨ valuation q 49 = true ∨ valuation q 106 = true := by
  rw [value33, value49, value50, value106, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (197 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(133 : Vertex), (196 : Vertex), (453 : Vertex)] := by decide
  have hg := other_cover q (197 : Vertex) (213 : Vertex) [(133 : Vertex), (196 : Vertex), (453 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 56 = false := by
  rw [value48, value49, value51, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (196 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 61 = false := by
  rw [value48, value49, value51, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (196 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 107 = false := by
  rw [value48, value49, value51, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (196 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 61 = false := by
  rw [value48, value51, value56, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 107 = false := by
  rw [value48, value51, value56, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (206 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 48 = false ∨ valuation q 61 = false ∨ valuation q 107 = false := by
  rw [value48, value51, value61, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (194 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 61 = false := by
  rw [value49, value51, value56, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (196 : Vertex) (206 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 56 = false ∨ valuation q 107 = false := by
  rw [value49, value51, value56, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (196 : Vertex) (206 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 49 = false ∨ valuation q 61 = false ∨ valuation q 107 = false := by
  rw [value49, value51, value61, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (196 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 61 = false ∨ valuation q 107 = false := by
  rw [value51, value56, value61, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (206 : Vertex) (214 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 61 = true ∨ valuation q 107 = true := by
  rw [value49, value51, value56, value61, value107, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (194 : Vertex) → w ∈ [(196 : Vertex), (206 : Vertex), (214 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (194 : Vertex) [(196 : Vertex), (206 : Vertex), (214 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 175 = true ∨ valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 56 = true ∨ valuation q 107 = true := by
  rw [value48, value49, value51, value56, value107, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (198 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(194 : Vertex), (196 : Vertex), (206 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (198 : Vertex) (214 : Vertex) [(194 : Vertex), (196 : Vertex), (206 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 52 = true := by
  rw [value52, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (200 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 63 = true := by
  rw [value47, value52, value53, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ∈ [(192 : Vertex), (202 : Vertex), (204 : Vertex), (216 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (200 : Vertex) [(192 : Vertex), (202 : Vertex), (204 : Vertex), (216 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 63 = false := by
  rw [value47, value52, value53, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (202 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value47, value52, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (192 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value52, value53, value55, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (200 : Vertex) (202 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value55, value63, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (200 : Vertex) (204 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 63 = true := by
  rw [value52, value53, value55, value63, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(202 : Vertex), (204 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(202 : Vertex), (204 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 55 = true ∨ valuation q 63 = true := by
  rw [value47, value52, value55, value63, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(192 : Vertex), (204 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (202 : Vertex) [(192 : Vertex), (204 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 63 = true := by
  rw [value47, value52, value53, value63, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(192 : Vertex), (202 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (204 : Vertex) [(192 : Vertex), (202 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 176 = true ∨ valuation q 47 = true ∨ valuation q 53 = true ∨ valuation q 55 = true := by
  rw [value47, value52, value53, value55, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(192 : Vertex), (202 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (216 : Vertex) [(192 : Vertex), (202 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value48, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (200 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 56 = false := by
  rw [value48, value52, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (202 : Vertex) (194 : Vertex) (200 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E105.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112105
