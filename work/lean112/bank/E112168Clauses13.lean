import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value99, value100, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (453 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 213 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value99, value104, value107, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (453 : Vertex) → w ∈ [(460 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (453 : Vertex) [(460 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 214 = true ∨ valuation q 83 = true ∨ valuation q 99 = true ∨ valuation q 108 = true := by
  rw [value83, value99, value100, value108, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(389 : Vertex), (452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (197 : Vertex) [(389 : Vertex), (452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 214 = true ∨ valuation q 46 = true ∨ valuation q 99 = true ∨ valuation q 108 = true := by
  rw [value46, value99, value100, value108, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(197 : Vertex), (452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (389 : Vertex) [(197 : Vertex), (452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 214 = true ∨ valuation q 46 = true ∨ valuation q 83 = true ∨ valuation q 108 = true := by
  rw [value46, value83, value100, value108, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(197 : Vertex), (389 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (452 : Vertex) [(197 : Vertex), (389 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 214 = true ∨ valuation q 46 = true ∨ valuation q 83 = true ∨ valuation q 99 = true := by
  rw [value46, value83, value99, value100, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(197 : Vertex), (389 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (469 : Vertex) [(197 : Vertex), (389 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 215 = true ∨ valuation q 71 = true ∨ valuation q 86 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value71, value86, value101, value103, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (201 : Vertex) → w ∈ [(329 : Vertex), (393 : Vertex), (459 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (201 : Vertex) [(329 : Vertex), (393 : Vertex), (459 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 215 = true ∨ valuation q 48 = true ∨ valuation q 71 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value48, value71, value101, value103, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex), (459 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (393 : Vertex) [(201 : Vertex), (329 : Vertex), (459 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 215 = true ∨ valuation q 48 = true ∨ valuation q 71 = true ∨ valuation q 86 = true ∨ valuation q 112 = true := by
  rw [value48, value71, value86, value101, value112, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex), (393 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (459 : Vertex) [(201 : Vertex), (329 : Vertex), (393 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 215 = true ∨ valuation q 48 = true ∨ valuation q 71 = true ∨ valuation q 86 = true ∨ valuation q 103 = true := by
  rw [value48, value71, value86, value101, value103, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (457 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(201 : Vertex), (329 : Vertex), (393 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (457 : Vertex) (473 : Vertex) [(201 : Vertex), (329 : Vertex), (393 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 216 = true ∨ valuation q 49 = true ∨ valuation q 103 = true ∨ valuation q 105 = true := by
  rw [value49, value102, value103, value105, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (450 : Vertex) → w ∈ [(202 : Vertex), (459 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (450 : Vertex) [(202 : Vertex), (459 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 216 = true ∨ valuation q 49 = true ∨ valuation q 97 = true ∨ valuation q 105 = true := by
  rw [value49, value97, value102, value105, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(202 : Vertex), (450 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (459 : Vertex) [(202 : Vertex), (450 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value98, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value98, value101, value103, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 98 = false ∨ valuation q 102 = false ∨ valuation q 113 = false := by
  rw [value98, value102, value103, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 113 = false := by
  rw [value101, value102, value103, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 218 = true ∨ valuation q 50 = true ∨ valuation q 105 = true := by
  rw [value50, value104, value105, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(204 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (452 : Vertex) [(204 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 218 = true ∨ valuation q 50 = true ∨ valuation q 99 = true := by
  rw [value50, value99, value104, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(204 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (462 : Vertex) [(204 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 52 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value52, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (206 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 219 = true ∨ valuation q 52 = true ∨ valuation q 104 = true := by
  rw [value52, value104, value105, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(206 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (458 : Vertex) [(206 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 219 = true ∨ valuation q 52 = true ∨ valuation q 102 = true := by
  rw [value52, value102, value105, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(206 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (460 : Vertex) [(206 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 99 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value99, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 100 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value100, value107, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 92 = false ∨ valuation q 107 = false ∨ valuation q 110 = false := by
  rw [value92, value107, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (406 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 224 = true ∨ valuation q 108 = true ∨ valuation q 109 = true := by
  rw [value108, value109, value110, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(469 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (479 : Vertex) [(469 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 225 = true ∨ valuation q 59 = true ∨ valuation q 112 = true := by
  rw [value59, value111, value112, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(216 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(216 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 60 = false ∨ valuation q 101 = false ∨ valuation q 111 = false := by
  rw [value60, value101, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (217 : Vertex) (457 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 60 = false ∨ valuation q 101 = false ∨ valuation q 113 = false := by
  rw [value60, value101, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (217 : Vertex) (457 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 60 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value60, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (217 : Vertex) (472 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 101 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value101, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (473 : Vertex) (457 : Vertex) (472 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 227 = true ∨ valuation q 103 = true ∨ valuation q 112 = true := by
  rw [value103, value112, value113, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(459 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (479 : Vertex) [(459 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 116 = false := by
  rw [value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (19 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block13 (q : Snake 81) (h : Conditions q) : B112E168.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112168
