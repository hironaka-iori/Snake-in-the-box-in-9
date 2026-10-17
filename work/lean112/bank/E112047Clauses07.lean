import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 29 = true ∨ valuation q 41 = true ∨ valuation q 48 = true := by
  rw [value29, value41, value47, value48, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(154 : Vertex), (210 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (216 : Vertex) [(154 : Vertex), (210 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 165 = true ∨ valuation q 29 = true ∨ valuation q 41 = true ∨ valuation q 45 = true := by
  rw [value29, value41, value45, value47, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(154 : Vertex), (210 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (219 : Vertex) [(154 : Vertex), (210 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 166 = true ∨ valuation q 47 = true := by
  rw [value47, value48, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(218 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (217 : Vertex) [(218 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 166 = true ∨ valuation q 46 = true := by
  rw [value46, value48, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 167 = true ∨ valuation q 46 = true := by
  rw [value46, value49, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (213 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 167 = true ∨ valuation q 42 = true := by
  rw [value42, value49, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (217 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 64 = false := by
  rw [value50, value51, value52, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 80 = false := by
  rw [value50, value51, value52, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 64 = false ∨ valuation q 80 = false := by
  rw [value50, value51, value64, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 64 = false ∨ valuation q 80 = false := by
  rw [value50, value52, value64, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (266 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 168 = true ∨ valuation q 52 = true ∨ valuation q 64 = true ∨ valuation q 80 = true := by
  rw [value50, value52, value64, value80, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(266 : Vertex), (322 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (259 : Vertex) [(266 : Vertex), (322 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 64 = true ∨ valuation q 80 = true := by
  rw [value50, value51, value64, value80, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(259 : Vertex), (322 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(259 : Vertex), (322 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 80 = true := by
  rw [value50, value51, value52, value80, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(259 : Vertex), (266 : Vertex), (386 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (322 : Vertex) [(259 : Vertex), (266 : Vertex), (386 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 168 = true ∨ valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 64 = true := by
  rw [value50, value51, value52, value64, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(259 : Vertex), (266 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (386 : Vertex) [(259 : Vertex), (266 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = true ∨ valuation q 55 = true ∨ valuation q 81 = true := by
  rw [value50, value51, value55, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ∈ [(258 : Vertex), (275 : Vertex), (387 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (259 : Vertex) [(258 : Vertex), (275 : Vertex), (387 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 81 = false := by
  rw [value50, value51, value55, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (259 : Vertex) (258 : Vertex) (275 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value50, value55, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (259 : Vertex) (258 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 55 = true ∨ valuation q 81 = true := by
  rw [value51, value55, value81, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(275 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(275 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 81 = true := by
  rw [value50, value51, value81, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(258 : Vertex), (387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (275 : Vertex) [(258 : Vertex), (387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 55 = true := by
  rw [value50, value51, value55, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(258 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (387 : Vertex) [(258 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 52 = true := by
  rw [value52, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (266 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = true ∨ valuation q 69 = true ∨ valuation q 87 = true := by
  rw [value50, value52, value69, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ∈ [(258 : Vertex), (330 : Vertex), (394 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (266 : Vertex) [(258 : Vertex), (330 : Vertex), (394 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = false ∨ valuation q 69 = false ∨ valuation q 87 = false := by
  rw [value50, value52, value69, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (266 : Vertex) (258 : Vertex) (330 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 69 = true ∨ valuation q 87 = true := by
  rw [value52, value69, value87, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(330 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(330 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 87 = true := by
  rw [value50, value52, value87, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(258 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (330 : Vertex) [(258 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 69 = true := by
  rw [value50, value52, value69, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(258 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (394 : Vertex) [(258 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 58 = false := by
  rw [value53, value54, value56, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (273 : Vertex) (276 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 56 = true ∨ valuation q 58 = true := by
  rw [value53, value56, value58, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (273 : Vertex) → w ∈ [(276 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (273 : Vertex) [(276 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 58 = true := by
  rw [value53, value54, value58, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(273 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(273 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 171 = true ∨ valuation q 54 = true ∨ valuation q 56 = true := by
  rw [value53, value54, value56, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(273 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(273 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 90 = false := by
  rw [value53, value54, value55, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (273 : Vertex) (272 : Vertex) (275 : Vertex) (401 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 172 = true ∨ valuation q 55 = true ∨ valuation q 90 = true := by
  rw [value54, value55, value90, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (273 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(275 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (273 : Vertex) (272 : Vertex) [(275 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E047.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112047
