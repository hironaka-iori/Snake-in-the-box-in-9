import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 222 = true ∨ valuation q 40 = true ∨ valuation q 108 = true := by
  rw [value40, value103, value108, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(195 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (450 : Vertex) [(195 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 222 = true ∨ valuation q 40 = true ∨ valuation q 102 = true := by
  rw [value40, value102, value103, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(195 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (459 : Vertex) [(195 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value104, value105, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (453 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 224 = true ∨ valuation q 87 = true ∨ valuation q 104 = true ∨ valuation q 113 = true := by
  rw [value87, value104, value105, value113, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(389 : Vertex), (452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (197 : Vertex) [(389 : Vertex), (452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 224 = true ∨ valuation q 41 = true ∨ valuation q 104 = true ∨ valuation q 113 = true := by
  rw [value41, value104, value105, value113, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(197 : Vertex), (452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (389 : Vertex) [(197 : Vertex), (452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 224 = true ∨ valuation q 41 = true ∨ valuation q 87 = true ∨ valuation q 113 = true := by
  rw [value41, value87, value105, value113, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(197 : Vertex), (389 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(197 : Vertex), (389 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 224 = true ∨ valuation q 41 = true ∨ valuation q 87 = true ∨ valuation q 104 = true := by
  rw [value41, value87, value104, value105, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(197 : Vertex), (389 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (469 : Vertex) [(197 : Vertex), (389 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 43 = false ∨ valuation q 108 = false ∨ valuation q 117 = false := by
  rw [value43, value106, value108, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (201 : Vertex) (459 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 225 = true ∨ valuation q 74 = true ∨ valuation q 91 = true ∨ valuation q 108 = true ∨ valuation q 117 = true := by
  rw [value74, value91, value106, value108, value117, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(329 : Vertex), (393 : Vertex), (459 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (201 : Vertex) [(329 : Vertex), (393 : Vertex), (459 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 225 = true ∨ valuation q 43 = true ∨ valuation q 74 = true ∨ valuation q 91 = true ∨ valuation q 117 = true := by
  rw [value43, value74, value91, value106, value117, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex), (393 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (459 : Vertex) [(201 : Vertex), (329 : Vertex), (393 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 225 = true ∨ valuation q 43 = true ∨ valuation q 74 = true ∨ valuation q 91 = true ∨ valuation q 108 = true := by
  rw [value43, value74, value91, value106, value108, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex), (393 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (473 : Vertex) [(201 : Vertex), (329 : Vertex), (393 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 226 = true ∨ valuation q 44 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value44, value107, value108, value110, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(202 : Vertex), (459 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (450 : Vertex) [(202 : Vertex), (459 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 226 = true ∨ valuation q 44 = true ∨ valuation q 102 = true ∨ valuation q 110 = true := by
  rw [value44, value102, value107, value110, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(202 : Vertex), (450 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (459 : Vertex) [(202 : Vertex), (450 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 226 = true ∨ valuation q 44 = true ∨ valuation q 102 = true ∨ valuation q 108 = true := by
  rw [value44, value102, value107, value108, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(202 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (462 : Vertex) [(202 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value103, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value103, value106, value108, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value103, value107, value108, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value106, value107, value108, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 45 = false ∨ valuation q 104 = false ∨ valuation q 110 = false := by
  rw [value45, value104, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (452 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 228 = true ∨ valuation q 104 = true ∨ valuation q 110 = true := by
  rw [value104, value109, value110, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (204 : Vertex) [(452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 228 = true ∨ valuation q 45 = true ∨ valuation q 110 = true := by
  rw [value45, value109, value110, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(204 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (452 : Vertex) [(204 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 228 = true ∨ valuation q 45 = true ∨ valuation q 104 = true := by
  rw [value45, value104, value109, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(204 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (462 : Vertex) [(204 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 47 = true ∨ valuation q 107 = true ∨ valuation q 109 = true := by
  rw [value47, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ∈ [(206 : Vertex), (458 : Vertex), (460 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (462 : Vertex) [(206 : Vertex), (458 : Vertex), (460 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 47 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value47, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 47 = false ∨ valuation q 107 = false := by
  rw [value47, value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (462 : Vertex) (206 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide)

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 47 = false ∨ valuation q 109 = false := by
  rw [value47, value109, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (462 : Vertex) (206 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide)

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 229 = true ∨ valuation q 107 = true ∨ valuation q 109 = true := by
  rw [value107, value109, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (206 : Vertex) → w ∈ [(458 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (206 : Vertex) [(458 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 229 = true ∨ valuation q 47 = true ∨ valuation q 109 = true := by
  rw [value47, value109, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(206 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (458 : Vertex) [(206 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 229 = true ∨ valuation q 47 = true ∨ valuation q 107 = true := by
  rw [value47, value107, value110, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(206 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (460 : Vertex) [(206 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 49 = false ∨ valuation q 112 = false ∨ valuation q 116 = false := by
  rw [value49, value111, value112, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (208 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 104 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value104, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 231 = true ∨ valuation q 104 = true ∨ valuation q 111 = true ∨ valuation q 113 = true := by
  rw [value104, value111, value112, value113, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(452 : Vertex), (464 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (470 : Vertex) [(452 : Vertex), (464 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block15 (q : Snake 81) (h : Conditions q) : B112E078.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112078
