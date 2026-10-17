import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = false ∨ valuation q 46 = false ∨ valuation q 116 = false := by
  rw [value43, value45, value46, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (218 : Vertex) (223 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 116 = false := by
  rw [value44, value45, value46, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (222 : Vertex) (220 : Vertex) (223 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 162 = true ∨ valuation q 16 = true ∨ valuation q 25 = true ∨ valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 46 = true := by
  rw [value16, value25, value41, value43, value44, value45, value46, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(94 : Vertex), (158 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (223 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (478 : Vertex) [(94 : Vertex), (158 : Vertex), (214 : Vertex), (218 : Vertex), (220 : Vertex), (223 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 163 = true ∨ valuation q 45 = true ∨ valuation q 117 = true := by
  rw [value45, value46, value117, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (223 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(222 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (223 : Vertex) (207 : Vertex) [(222 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 163 = true ∨ valuation q 36 = true ∨ valuation q 45 = true := by
  rw [value36, value45, value46, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (223 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(207 : Vertex), (222 : Vertex)] := by decide
  have hg := other_cover q (223 : Vertex) (479 : Vertex) [(207 : Vertex), (222 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 66 = false := by
  rw [value47, value50, value52, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 164 = true ∨ valuation q 52 = true ∨ valuation q 66 = true := by
  rw [value47, value52, value66, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(266 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (262 : Vertex) [(266 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 164 = true ∨ valuation q 50 = true ∨ valuation q 66 = true := by
  rw [value47, value50, value66, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(262 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(262 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value49, value50, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (260 : Vertex) (261 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 50 = true := by
  rw [value48, value50, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(262 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (261 : Vertex) [(262 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 165 = true ∨ valuation q 49 = true := by
  rw [value48, value49, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (260 : Vertex) w → w ∈ region → w ≠ (262 : Vertex) → w ∈ [(261 : Vertex)] := by decide
  have hg := other_cover q (260 : Vertex) (262 : Vertex) [(261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 166 = true ∨ valuation q 58 = true := by
  rw [value49, value58, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (260 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 166 = true ∨ valuation q 48 = true := by
  rw [value48, value49, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (277 : Vertex) [(260 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value48, value50, value54, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(260 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (258 : Vertex) [(260 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 47 = true ∨ valuation q 54 = true := by
  rw [value47, value50, value54, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(258 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (260 : Vertex) [(258 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 167 = true ∨ valuation q 47 = true ∨ valuation q 48 = true := by
  rw [value47, value48, value50, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex), (260 : Vertex)] := by decide
  have hg := other_cover q (262 : Vertex) (270 : Vertex) [(258 : Vertex), (260 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 61 = false ∨ valuation q 69 = false := by
  rw [value51, value53, value61, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (265 : Vertex) (267 : Vertex) (281 : Vertex) (329 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 168 = true ∨ valuation q 61 = true ∨ valuation q 69 = true := by
  rw [value51, value61, value69, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(281 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (267 : Vertex) [(281 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 168 = true ∨ valuation q 53 = true ∨ valuation q 69 = true := by
  rw [value51, value53, value69, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (265 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(267 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (265 : Vertex) (281 : Vertex) [(267 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 47 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value47, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (267 : Vertex) (270 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 53 = true ∨ valuation q 54 = true := by
  rw [value52, value53, value54, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(267 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(267 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 47 = true ∨ valuation q 54 = true := by
  rw [value47, value52, value54, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(258 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (267 : Vertex) [(258 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 169 = true ∨ valuation q 47 = true ∨ valuation q 53 = true := by
  rw [value47, value52, value53, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (270 : Vertex) [(258 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 53 = true := by
  rw [value53, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (267 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 70 = true := by
  rw [value51, value52, value53, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ∈ [(265 : Vertex), (266 : Vertex), (331 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (267 : Vertex) [(265 : Vertex), (266 : Vertex), (331 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 70 = false := by
  rw [value51, value52, value53, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (265 : Vertex) (266 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value51, value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (267 : Vertex) (265 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 170 = true ∨ valuation q 52 = true ∨ valuation q 70 = true := by
  rw [value52, value53, value70, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(266 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (265 : Vertex) [(266 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 170 = true ∨ valuation q 51 = true ∨ valuation q 70 = true := by
  rw [value51, value53, value70, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(265 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (266 : Vertex) [(265 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 62 = false := by
  rw [value50, value52, value54, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value50, value52, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (270 : Vertex) (262 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 171 = true ∨ valuation q 50 = true ∨ valuation q 62 = true := by
  rw [value50, value54, value62, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(262 : Vertex), (286 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (266 : Vertex) [(262 : Vertex), (286 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E064.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112064
