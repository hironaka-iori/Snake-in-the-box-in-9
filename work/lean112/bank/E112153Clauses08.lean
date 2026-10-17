import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 71 = true ∨ valuation q 74 = true := by
  rw [value71, value74, value78, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (345 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(329 : Vertex), (337 : Vertex)] := by decide
  have hg := other_cover q (345 : Vertex) (349 : Vertex) [(329 : Vertex), (337 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 123 = false := by
  rw [value79, value80, value81, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (348 : Vertex) (349 : Vertex) (350 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value80, value81, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (348 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 81 = true ∨ valuation q 123 = true := by
  rw [value79, value81, value123, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(350 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(350 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 80 = true ∨ valuation q 123 = true := by
  rw [value79, value80, value123, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(349 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(349 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value77, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (341 : Vertex) (345 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 78 = true ∨ valuation q 79 = true := by
  rw [value78, value79, value80, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(345 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (341 : Vertex) [(345 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value77, value79, value80, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(341 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (345 : Vertex) [(341 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 204 = true ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value77, value78, value80, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(341 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (348 : Vertex) [(341 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 79 = true ∨ valuation q 124 = true := by
  rw [value79, value81, value124, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(348 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (334 : Vertex) [(348 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 72 = true ∨ valuation q 124 = true := by
  rw [value72, value81, value124, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(334 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (348 : Vertex) [(334 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 72 = true ∨ valuation q 79 = true := by
  rw [value72, value79, value81, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(334 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (478 : Vertex) [(334 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 102 = false := by
  rw [value82, value83, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (388 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 84 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value82, value84, value92, value102, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (386 : Vertex) → w ∈ [(388 : Vertex), (400 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (386 : Vertex) [(388 : Vertex), (400 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 83 = true ∨ valuation q 92 = true ∨ valuation q 102 = true := by
  rw [value82, value83, value92, value102, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(386 : Vertex), (400 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (388 : Vertex) [(386 : Vertex), (400 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 102 = true := by
  rw [value82, value83, value84, value102, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [(386 : Vertex), (388 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 92 = true := by
  rw [value82, value83, value84, value92, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (448 : Vertex) → w ∈ [(386 : Vertex), (388 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (448 : Vertex) [(386 : Vertex), (388 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = true ∨ valuation q 87 = true ∨ valuation q 94 = true := by
  rw [value82, value83, value87, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ∈ [(384 : Vertex), (394 : Vertex), (402 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (386 : Vertex) [(384 : Vertex), (394 : Vertex), (402 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 87 = false ∨ valuation q 94 = false := by
  rw [value82, value83, value87, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (394 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 87 = true ∨ valuation q 94 = true := by
  rw [value83, value87, value94, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(394 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(394 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 82 = true ∨ valuation q 87 = true := by
  rw [value82, value83, value87, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(384 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (402 : Vertex) [(384 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 82 = false ∨ valuation q 88 = false := by
  rw [value14, value82, value84, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 82 = false ∨ valuation q 105 = false := by
  rw [value14, value82, value84, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value82, value84, value88, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (396 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 82 = false ∨ valuation q 105 = false := by
  rw [value82, value105, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (388 : Vertex) (384 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide)

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 14 = true ∨ valuation q 88 = true ∨ valuation q 105 = true := by
  rw [value14, value84, value88, value105, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(132 : Vertex), (396 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (384 : Vertex) [(132 : Vertex), (396 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 14 = true ∨ valuation q 82 = true ∨ valuation q 88 = true := by
  rw [value14, value82, value84, value88, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(132 : Vertex), (384 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (452 : Vertex) [(132 : Vertex), (384 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 91 = false ∨ valuation q 96 = false ∨ valuation q 107 = false := by
  rw [value85, value91, value96, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (391 : Vertex) (399 : Vertex) (407 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 51 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value51, value85, value96, value107, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (391 : Vertex) w → w ∈ region → w ≠ (399 : Vertex) → w ∈ [(263 : Vertex), (407 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (391 : Vertex) (399 : Vertex) [(263 : Vertex), (407 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 109 = false := by
  rw [value86, value89, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (393 : Vertex) (397 : Vertex) (409 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 97 = true ∨ valuation q 109 = true := by
  rw [value86, value97, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(409 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (397 : Vertex) [(409 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 89 = true ∨ valuation q 109 = true := by
  rw [value86, value89, value109, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (393 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(397 : Vertex), (457 : Vertex)] := by decide
  have hg := other_cover q (393 : Vertex) (409 : Vertex) [(397 : Vertex), (457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E153.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112153
