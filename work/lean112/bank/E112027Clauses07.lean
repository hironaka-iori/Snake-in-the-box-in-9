import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 82 = false := by
  rw [value51, value55, value56, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 82 = true := by
  rw [value51, value52, value55, value56, value82, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (2 : Vertex) → w ∈ [(259 : Vertex), (262 : Vertex), (266 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (2 : Vertex) [(259 : Vertex), (262 : Vertex), (266 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 3 = true ∨ valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 82 = true := by
  rw [value3, value51, value55, value56, value82, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(2 : Vertex), (262 : Vertex), (266 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (259 : Vertex) [(2 : Vertex), (262 : Vertex), (266 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 3 = true ∨ valuation q 52 = true ∨ valuation q 56 = true ∨ valuation q 82 = true := by
  rw [value3, value51, value52, value56, value82, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(2 : Vertex), (259 : Vertex), (266 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (262 : Vertex) [(2 : Vertex), (259 : Vertex), (266 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 3 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 82 = true := by
  rw [value3, value51, value52, value55, value82, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(2 : Vertex), (259 : Vertex), (262 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(2 : Vertex), (259 : Vertex), (262 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 52 = true := by
  rw [value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (259 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 51 = true ∨ valuation q 83 = true := by
  rw [value51, value52, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ∈ [(258 : Vertex), (387 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (259 : Vertex) [(258 : Vertex), (387 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 51 = false ∨ valuation q 83 = false := by
  rw [value51, value83, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (259 : Vertex) (258 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 83 = true := by
  rw [value52, value83, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 51 = true := by
  rw [value51, value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(258 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (387 : Vertex) [(258 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 57 = false := by
  rw [value53, value54, value55, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (268 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 59 = false := by
  rw [value53, value55, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (262 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 59 = true := by
  rw [value53, value55, value57, value59, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(262 : Vertex), (268 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (261 : Vertex) [(262 : Vertex), (268 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 57 = true ∨ valuation q 59 = true := by
  rw [value53, value54, value57, value59, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(261 : Vertex), (268 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (262 : Vertex) [(261 : Vertex), (268 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value53, value54, value55, value57, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (262 : Vertex), (268 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (276 : Vertex) [(261 : Vertex), (262 : Vertex), (268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 54 = true := by
  rw [value54, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (261 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value53, value54, value60, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (277 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 60 = false ∨ valuation q 84 = false := by
  rw [value53, value54, value60, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (260 : Vertex) (277 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 60 = false ∨ valuation q 65 = false := by
  rw [value60, value65, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (261 : Vertex) (277 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 60 = false ∨ valuation q 84 = false := by
  rw [value60, value84, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (261 : Vertex) (277 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 60 = true ∨ valuation q 65 = true ∨ valuation q 84 = true := by
  rw [value54, value60, value65, value84, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(277 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (260 : Vertex) [(277 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 53 = true ∨ valuation q 65 = true ∨ valuation q 84 = true := by
  rw [value53, value54, value65, value84, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (325 : Vertex), (389 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (277 : Vertex) [(260 : Vertex), (325 : Vertex), (389 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 4 = false ∨ valuation q 51 = false ∨ valuation q 66 = false := by
  rw [value4, value51, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (258 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 4 = false ∨ valuation q 53 = false ∨ valuation q 66 = false := by
  rw [value4, value53, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (260 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 4 = false ∨ valuation q 58 = false ∨ valuation q 66 = false := by
  rw [value4, value55, value58, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (270 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 66 = false := by
  rw [value51, value53, value55, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (260 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 51 = false ∨ valuation q 58 = false ∨ valuation q 66 = false := by
  rw [value51, value55, value58, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (258 : Vertex) (270 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 53 = false ∨ valuation q 58 = false ∨ valuation q 66 = false := by
  rw [value53, value55, value58, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (260 : Vertex) (270 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 4 = true ∨ valuation q 51 = true ∨ valuation q 58 = true ∨ valuation q 66 = true := by
  rw [value4, value51, value55, value58, value66, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(6 : Vertex), (258 : Vertex), (270 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (260 : Vertex) [(6 : Vertex), (258 : Vertex), (270 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 4 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 66 = true := by
  rw [value4, value51, value53, value55, value66, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(6 : Vertex), (258 : Vertex), (260 : Vertex), (326 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (270 : Vertex) [(6 : Vertex), (258 : Vertex), (260 : Vertex), (326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 173 = true ∨ valuation q 4 = true ∨ valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 58 = true := by
  rw [value4, value51, value53, value55, value58, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(6 : Vertex), (258 : Vertex), (260 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (326 : Vertex) [(6 : Vertex), (258 : Vertex), (260 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 56 = true := by
  rw [value56, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (266 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem block7 (q : Snake 81) (h : Conditions q) : B112E027.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112027
