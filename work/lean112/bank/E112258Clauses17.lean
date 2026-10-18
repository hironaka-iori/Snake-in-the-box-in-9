import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value89, value95, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 221 = true ∨ valuation q 95 = true ∨ valuation q 101 = true := by
  rw [value95, value99, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(435 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(435 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 221 = true ∨ valuation q 89 = true ∨ valuation q 101 = true := by
  rw [value89, value99, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(427 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (435 : Vertex) [(427 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 221 = true ∨ valuation q 89 = true ∨ valuation q 95 = true := by
  rw [value89, value95, value99, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (447 : Vertex) [(427 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 79 = false ∨ valuation q 90 = false ∨ valuation q 98 = false := by
  rw [value79, value90, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (412 : Vertex) (428 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 222 = true ∨ valuation q 90 = true ∨ valuation q 98 = true := by
  rw [value90, value98, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(428 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (412 : Vertex) [(428 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 222 = true ∨ valuation q 79 = true ∨ valuation q 90 = true := by
  rw [value79, value90, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(412 : Vertex), (428 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (440 : Vertex) [(412 : Vertex), (428 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 41 = false ∨ valuation q 81 = false ∨ valuation q 99 = false := by
  rw [value41, value81, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (319 : Vertex) (415 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 41 = false ∨ valuation q 99 = false := by
  rw [value41, value99, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (447 : Vertex) (319 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 81 = true ∨ valuation q 99 = true := by
  rw [value81, value99, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (319 : Vertex) → w ∈ [(415 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (319 : Vertex) [(415 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 41 = true ∨ valuation q 99 = true := by
  rw [value41, value99, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(319 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (415 : Vertex) [(319 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 223 = true ∨ valuation q 41 = true ∨ valuation q 81 = true := by
  rw [value41, value81, value101, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(319 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (443 : Vertex) [(319 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 224 = true ∨ valuation q 64 = true ∨ valuation q 103 = true ∨ valuation q 110 = true := by
  rw [value64, value102, value103, value110, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(384 : Vertex), (452 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (320 : Vertex) [(384 : Vertex), (452 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 224 = true ∨ valuation q 42 = true ∨ valuation q 103 = true ∨ valuation q 110 = true := by
  rw [value42, value102, value103, value110, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(320 : Vertex), (452 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (384 : Vertex) [(320 : Vertex), (452 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 224 = true ∨ valuation q 42 = true ∨ valuation q 64 = true ∨ valuation q 110 = true := by
  rw [value42, value64, value102, value110, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(320 : Vertex), (384 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (452 : Vertex) [(320 : Vertex), (384 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 224 = true ∨ valuation q 42 = true ∨ valuation q 64 = true ∨ valuation q 103 = true := by
  rw [value42, value64, value102, value103, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(320 : Vertex), (384 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (448 : Vertex) (480 : Vertex) [(320 : Vertex), (384 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value67, value102, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (448 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 67 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value67, value102, value103, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (448 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 67 = false ∨ valuation q 105 = false ∨ valuation q 112 = false := by
  rw [value67, value103, value105, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (388 : Vertex) (468 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 112 = false := by
  rw [value102, value103, value105, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (448 : Vertex) (468 : Vertex) (484 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true := by
  rw [value104, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (462 : Vertex) (478 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 75 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value75, value103, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (452 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 75 = false ∨ valuation q 103 = false ∨ valuation q 118 = false := by
  rw [value75, value103, value105, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (452 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 75 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value75, value105, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (469 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 227 = true ∨ valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 118 = true := by
  rw [value103, value105, value106, value118, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(452 : Vertex), (469 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (404 : Vertex) [(452 : Vertex), (469 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 227 = true ∨ valuation q 75 = true ∨ valuation q 103 = true ∨ valuation q 118 = true := by
  rw [value75, value103, value105, value118, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(404 : Vertex), (452 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (469 : Vertex) [(404 : Vertex), (452 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 228 = true ∨ valuation q 105 = true := by
  rw [value105, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (341 : Vertex) → w ∈ [(468 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (341 : Vertex) [(468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 229 = true := by
  rw [value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (472 : Vertex) (344 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 80 = false ∨ valuation q 109 = false ∨ valuation q 122 = false := by
  rw [value80, value108, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (478 : Vertex) (414 : Vertex) (479 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 230 = true ∨ valuation q 80 = true ∨ valuation q 109 = true ∨ valuation q 122 = true := by
  rw [value80, value108, value109, value122, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(414 : Vertex), (479 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (462 : Vertex) [(414 : Vertex), (479 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 230 = true ∨ valuation q 80 = true ∨ valuation q 104 = true ∨ valuation q 122 = true := by
  rw [value80, value104, value108, value122, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(414 : Vertex), (462 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (479 : Vertex) [(414 : Vertex), (462 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 230 = true ∨ valuation q 80 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value80, value104, value108, value109, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(414 : Vertex), (462 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (510 : Vertex) [(414 : Vertex), (462 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block17 (q : Snake 81) (h : Conditions q) : B112E258.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112258
